{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveFoldable, FlexibleContexts #-}

-- | This module provides IO primitives and an effectful evaluator for the core data representation from 'Goat.Eval.Dyn'.
module Goat.Eval.IO.Dyn
  ( evalIO
  , io
  , ioMode
  , runDynIO
  , DynIO
  , dynIO
  )
  where

import Goat.Dyn.DynMap
import Goat.Error
import Goat.Eval.Dyn
import Goat.Syntax.Patterns
import qualified Goat.Syntax.Class as S
import Goat.Util ((<&>), Compose(..))
import Control.Applicative (liftA2, (<|>))
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Bitraversable
import Data.IORef
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Data.Semigroup (Option(..), Last(..))
import System.IO hiding (openFile)



evalIO
  :: (S.Self k, Ord k)
  => Syn (Res k) (Eval (DynIO k))
  -> ([StaticError k], IO (Maybe (DynError k)))
evalIO m = liftA2
  (\ ev en -> runDynIO (self (ev [(en,r0)])))
  (runRes (readSyn m) [["io", "ioMode"]])
  (runRes (readSyn imports) [])
  where
    imports = traverse (fmap (\ ev -> ev [])) [io, ioMode]
    
    r0 = (Repr . Block . const . dyn) (DynMap Nothing M.empty)


type DynIO k = Dyn k (Run k)
data Run k a = Run
  (Maybe (IO (Maybe (DynError k))))
  a
  deriving (Functor, Foldable)
  
instance Applicative (Run k) where
  pure = Run Nothing
  Run m f <*> Run m' a = Run (m' <|> m) (f a)


dynIO :: IO (Maybe (DynError k)) -> DynIO k a
dynIO io = Compose (Run
  (Just io)
  (Compose (DynMap Nothing M.empty)))
    
runDynIO :: Self (DynIO k) -> IO (Maybe (DynError k))
runDynIO (Block (Compose (Run (Just io) _))) = io
runDynIO v                                   = return (checke v)


io
 :: (S.Self k, Ord k) => Syn (Res k) (Eval (DynIO k))
io = do 
  eva <- async
  mkH <- makeHandle eva
  mkR <- makeRef eva
  S.block_
    [ S.self_ "openFile" S.#= S.esc_ (openFile mkH <&> (`id` eva))
    , S.self_ "stdout" S.#= S.esc_ (pure (mkH stdout))
    , S.self_ "stdin" S.#= S.esc_ (pure (mkH stdin))
    , S.self_ "stderr" S.#= S.esc_ (pure (mkH stderr))
    , S.self_ "newMut" S.#= S.esc_ (pure (newMut mkR eva))
    ]
  where
    async = S.block_
      [ S.self_ "onSuccess" S.#= S.esc_ (S.block_ [])
      , S.self_ "onError" S.#= S.esc_ (S.block_ [])
      ]

ioMode
 :: (S.Self k, Ord k) => Syn (Res k) (Eval (DynIO k))
ioMode = S.block_
  [ S.self_ "read" S.#= S.esc_ (S.block_
      [ S.self_ "match" S.#= S.self_ "ifRead" ])
  , S.self_ "write" S.#= S.esc_ (S.block_
      [ S.self_ "match" S.#= S.self_ "ifWrite" ])
  , S.self_ "append" S.#= S.esc_ (S.block_
      [ S.self_ "match" S.#= S.self_ "ifAppend" ])
  , S.self_ "readWrite" S.#= S.esc_ (S.block_
      [ S.self_ "match" S.#= S.self_ "ifReadWrite" ])
  ]

    
openFile
 :: forall k
  . (S.Self k, Ord k)
 => (Handle -> Reader (Scopes (DynIO k)) (DynIO k))
 -> Syn (Res k)
      (Reader (Scopes (DynIO k)) (DynIO k)
       -> Reader (Scopes (DynIO k)) (DynIO k))
openFile mkHandle = run <&> liftA2 (S.#)
  where
    run :: Syn (Res k) (Reader (Scopes (DynIO k)) (DynIO k))
    run = S.block_
      [ S.self_ "run" S.#=
          S.self_ "mode" S.# S.block_
            [ S.self_ "ifRead" S.#=
              S.esc_ (pure (open ReadMode))
            , S.self_ "ifWrite" S.#=
              S.esc_ (pure (open WriteMode))
            , S.self_ "ifAppend" S.#=
              S.esc_ (pure (open AppendMode))
            , S.self_ "ifReadWrite" S.#=
              S.esc_ (pure (open ReadWriteMode))
            ] S.#. "match"
      ]
      
    open
      :: (S.Self k, Ord k) => IOMode -> Reader (Scopes (DynIO k)) (DynIO k)
    open mode = do
      scopes <- ask
      se <- asks getSelf
      return (strk (self (se S.#. "file"))
        (\ t -> (Repr
          . Block
          . const
          . dynIO
          . withFile (T.unpack t) mode)
          (\ h -> (runDynIO . self) (se
            S.# mkHandle h scopes
            S.#. "onSuccess"))))

          
makeBlock
 :: (S.Self k, Ord k, Applicative f, Foldable f)
 => [ Stmt [Path k] 
      ( Patt (Decomps k) Bind
      , Syn (Res k) (a -> Reader (Scopes (Dyn k f)) (Dyn k f))
      )
    ]
 -> Syn (Res k) (a -> Reader (Scopes (Dyn k f)) (Dyn k f))
makeBlock rs = (Syn . fmap reader) (liftA2 evalTup
  (dynCheckTup (fmap (fmap pure) c))
  (traverse
    (bitraverse dynCheckPatt readSyn)
    pas))
  where
    (c, pas) = buildComps rs
    
    evalTup kv pas a scopes = 
      (Repr . Block) (\ se -> 
        (fmap (values se !!)
        . dyn) (DynMap Nothing kv))
      where
        values se = foldMap
          (\ (p, f) ->
            match p (f a scopes'))
          pas
          where
            scopes' = ([],se):scopes

makeHandle
 :: (S.Self k, Ord k)
 => Reader (Scopes (DynIO k)) (DynIO k)
 -> Syn (Res k) (Handle -> Reader (Scopes (DynIO k)) (DynIO k))
makeHandle ev' = makeBlock
  [ S.self_ "getLine" S.#= runs hGetLine
  , S.self_ "getContents" S.#= runs hGetContents
  , S.self_ "putText" S.#= runs hPutStr
  ]
  where
    runs f = makeBlock [ S.self_ "run" S.#= pure f ] 
      <&> (\ f h -> liftA2 (S.#) ev' (f h))
  
    hGetLine
      :: (S.Self k, Ord k) => Handle -> Eval (DynIO k)
    hGetLine h = do
      se <- asks getSelf
      scopes <- ask
      (return
        . Repr
        . Block
        . const
        . dynIO) 
        (do
          t <- T.hGetLine h
          (runDynIO . self) (se
            S.# runReader (field (S.self_ "text") (pure (Repr (Text t))))
              scopes
            S.#. "onSuccess"))
      
    hGetContents
     :: (S.Self k, Ord k) => Handle -> Reader (Scopes (DynIO k)) (DynIO k)
    hGetContents h = do
      scopes <- ask
      se <- asks getSelf
      (return 
        . Repr
        . Block
        . const
        . dynIO)
        (do
            t <- T.hGetContents h
            (runDynIO . self) (se
              S.# runReader (field (S.self_ "text") (pure (Repr (Text t))))
                scopes
              S.#. "onSuccess"))
  
    hPutStr
     :: (S.Self k, Ord k)
     => Handle -> Reader (Scopes (DynIO k)) (DynIO k)
    hPutStr h = do
      se <- ask getSelf
      return (strk (self (se S.#. "text")) (\ t ->
        (Repr
        . Block
        . const 
        . dynIO)
          (T.hPutStr h t
            >> (runDynIO . self) (se S.#. "onSuccess"))))
      
      
field
  :: k -> (Reader (Scopes (DynIO k)) (DynIO k))
  -> Reader (Scopes (DynIO k)) (DynIO k)
field k ev = do
  scopes <- ask
  (Repr . Block) (\ se ->
    (dyn
    . DynMap Nothing
    . M.singleton k . pure . runReader ev) (([],se):scopes))
      
      
strk 
  :: Self (DynIO k)
  -> (T.Text -> Repr (DynIO k))
  -> Repr (DynIO k)
strk (Text t) k = k t
strk v        _ = Repr (maybe
  (const <$> typee NotText)
  (Block . const . throwDyn)
  (checke v))
  

newMut
  :: (S.Self k, Ord k)
  => (IORef (Repr (DynIO k)) -> Reader (Scopes (DynIO k)) (DynIO k))
  -> Reader (Scopes (DynIO k)) (DynIO k)
  -> Reader (Scopes (DynIO k)) (DynIO k)
newMut mkRef ev' = liftA2 (S.#) ev' (field (S.self_ "run") (reader ev))
  where
    ev = do
      scopes <- ask
      se <- asks getSelf
      (return
        . Repr
        . Block
        . const
        . dynIO)
        (do
          ref <- newIORef (se S.# "val")
          (runDynIO . self)
            (se
              S.# runReader (mkRef ref) scopes
              S.#. "onSuccess"))
  
  
makeRef
 :: (S.Self k, Ord k)
 => Reader (Scopes (DynIO k)) (DynIO k)
 -> Syn (Res k)
      (IORef (Repr (DynIO k)) -> Reader (Scopes (DynIO k)) (DynIO k))
makeRef ev' = makeBlock
  [ S.self_ "set" S.#= runs setMut
  , S.self_ "get" S.#= runs getMut
  ] 
  where
    runs f = makeBlock [ S.self_ "run" S.#= pure f ]
      <&> (\ f ref -> liftA2 (S.#) ev' (f ref))
  
    setMut
      :: (S.Self k, Ord k)
      => IORef (Repr (DynIO k))
      -> Reader (Scopes (DynIO k)) (DynIO k)
    setMut ref = do
      se <- ask getSelf
      (return
        . Repr
        . Block
        . const
        . dynIO)
          (writeIORef ref (se S.#. "val")
            >> (runDynIO . self) (se S.#. "onSuccess"))
          
    getMut
      :: (S.Self k, Ord k)
      => IORef (Repr (DynIO k))
      -> Reader (Scopes (DynIO k)) (DynIO k)
    getMut ref = do
      scopes <- ask
      se <- asks getSelf
      (return 
        . Repr
        . Block
        . const
        . dynIO)
        (do 
          v <- readIORef ref
          (runDynIO . self)
            (se
              S.# runReader (field (S.self_ "val") (pure v)) scopes
              S.#. "onSuccess"))
  