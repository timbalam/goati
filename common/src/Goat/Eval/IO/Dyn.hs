{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveFoldable, FlexibleContexts #-}

-- | This module provides IO primitives and an effectful evaluator for the core data representation from 'Goat.Eval.Dyn'.
module Goat.Eval.IO.Dyn
  ( evalIO
  , io
  , ioMode
  , runDynIO
  , DynIO
  , dynIO
  , matchPlain
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
import Data.Functor.Identity
import Data.Bitraversable
import Data.IORef
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Data.Semigroup (Option(..), Last(..))
import System.IO hiding (openFile)



evalIO
  :: (S.Self k, Ord k)
  => Synt (Res k) (Eval (DynIO k))
  -> ([StaticError k], IO (Maybe (DynError k)))
evalIO (Synt m) = liftA2
  (\ ev mods -> runDynIO (self (runEval ev mods [])))
  (runRes m ["io", "ioMode"] [])
  (runRes imports [] [])
  where
    imports = traverse
      (fmap (\ ev -> runEval ev [] []) . readSynt)
      [io, ioMode]


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
 :: (S.Self k, Ord k) => Synt (Res k) (Eval (DynIO k))
io = Synt (do 
  eva <- readSynt async
  mkH <- readSynt (makeHandle eva)
  mkR <- readSynt (makeRef eva)
  readSynt (S.block_
    [ S.self_ "openFile" S.#=
        S.esc_ (Synt (readSynt (openFile mkH) <&> (`id` eva)))
    , S.self_ "stdout" S.#= S.esc_ (Synt (pure (mkH stdout)))
    , S.self_ "stdin" S.#= S.esc_ (Synt (pure (mkH stdin)))
    , S.self_ "stderr" S.#= S.esc_ (Synt (pure (mkH stderr)))
    , S.self_ "newMut" S.#= S.esc_ (Synt (pure (newMut mkR eva)))
    ]))
  where
    async = S.block_
      [ S.self_ "onSuccess" S.#= S.esc_ (S.block_ [])
      , S.self_ "onError" S.#= S.esc_ (S.block_ [])
      ]

ioMode
 :: (S.Self k, Ord k) => Synt (Res k) (Eval (DynIO k))
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
 => (Handle -> Eval (DynIO k))
 -> Synt (Res k) (Eval (DynIO k) -> Eval (DynIO k))
openFile mkHandle = Synt (readSynt run <&> liftA2 (S.#))
  where
    run :: Synt (Res k) (Eval (DynIO k))
    run = S.block_
      [ S.self_ "run" S.#=
          S.self_ "mode" S.# S.block_
            [ S.self_ "ifRead" S.#=
              S.esc_ (Synt (pure (open ReadMode)))
            , S.self_ "ifWrite" S.#=
              S.esc_ (Synt (pure (open WriteMode)))
            , S.self_ "ifAppend" S.#=
              S.esc_ (Synt (pure (open AppendMode)))
            , S.self_ "ifReadWrite" S.#=
              S.esc_ (Synt (pure (open ReadWriteMode)))
            ] S.#. "match"
      ]
      
    open
      :: (S.Self k, Ord k) => IOMode -> Eval (DynIO k)
    open mode = (do
      r <- ask
      se <- asks (getSelf . snd)
      return (strk (self (se S.#. "file"))
        (\ t ->
          (Repr
            . Block
            . const
            . dynIO
            . withFile (T.unpack t) mode)
            (\ h -> (runDynIO . self)
              (runReader (f (mkHandle h)) r)))))
        where
          f
           :: (S.Self k, Ord k)
           => Eval (DynIO k) -> Eval (DynIO k)
          f ev =
            liftA2 (S.#)
              (asks (getSelf . snd))
              ev
              <&> (S.#. "onSuccess")

          
makeBlock
 :: (S.Self k, Ord k, Applicative f, Foldable f)
 => [ Stmt [Path k] 
      ( Plain Bind
      , Synt (Res k) (a -> Eval (Dyn k f))
      )
    ]
 -> Synt (Res k) (a -> Eval (Dyn k f))
makeBlock rs = Synt (liftA2 evalTup
  (dynCheckTup (c <&> fmap pure))
  (traverse (traverse readSynt) pas)
    <&> (\ f a -> reader (f a)))
  where
    (c, pas) = buildComps rs
    
    evalTup kv pfs a (mods, scopes) = 
      (Repr . Block) (\ se -> 
        (fmap (values se !!)
        . dyn) (DynMap Nothing kv))
      where
        values se = runReader
          (matched
            (map (\ (p, f) -> matchPlain p <$> f a) pfs))
          (mods, scopes')
          where
            scopes' = ([],se):scopes

matchPlain :: Plain Bind -> a -> [a]
matchPlain (Plain Skip) _ = []
matchPlain (Plain Bind) a = [a]

makeHandle
 :: (S.Self k, Ord k)
 => Eval (DynIO k)
 -> Synt (Res k) (Handle -> Eval (DynIO k))
makeHandle ev' = makeBlock
  [ S.self_ "getLine" S.#= runs hGetLine
  , S.self_ "getContents" S.#= runs hGetContents
  , S.self_ "putText" S.#= runs hPutStr
  ]
  where
    runs f = Synt
      (readSynt (makeBlock [ S.self_ "run" S.#= Synt (pure f) ])
        <&> (\ f' h -> liftA2 (S.#) ev' (f' h)))
  
    hGetLine
      :: (S.Self k, Ord k) => Handle -> Eval (DynIO k)
    hGetLine h = reader (\ r ->
      (Repr
        . Block
        . const
        . dynIO) 
        (do
          t <- T.hGetLine h
          (runDynIO . self) 
            (runReader (f (pure (Repr (Text t)))) r)))
        where
          f
           :: (S.Self k, Ord k)
           => Eval (DynIO k) -> Eval (DynIO k)
          f ev =
            liftA2 (S.#)
              (asks (getSelf . snd))
              (field (S.self_ "text") ev)
              <&> (S.#. "onSuccess")
            
      
    hGetContents
     :: (S.Self k, Ord k) => Handle -> Eval (DynIO k)
    hGetContents h = reader (\ r ->
      (Repr
        . Block
        . const
        . dynIO)
        (do
          t <- T.hGetContents h
          (runDynIO . self)
            (runReader (f (pure (Repr (Text t)))) r)))
        where
          f :: (S.Self k, Ord k) => Eval (DynIO k) -> Eval (DynIO k)
          f ev =
            liftA2 (S.#)
              (asks (getSelf . snd))
              (field (S.self_ "text") ev)
              <&> (S.#. "onSuccess")
                
  
    hPutStr
     :: (S.Self k, Ord k)
     => Handle -> Eval (DynIO k)
    hPutStr h = do
      se <- asks (getSelf . snd)
      return
        (strk
          (self (se S.#. "text"))
          (\ t ->
            (Repr
            . Block
            . const 
            . dynIO)
              (T.hPutStr h t
                >> (runDynIO . self) (se S.#. "onSuccess"))))
      
      
field
  :: k -> Eval (DynIO k) -> Eval (DynIO k)
field k ev = reader (\ (mods, scopes) ->
  (Repr . Block) (\ se ->
    (dyn
    . DynMap Nothing
    . M.singleton k
    . pure
    . runReader ev)
      (mods, ([],se):scopes)))
      
      
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
 :: forall k . (S.Self k, Ord k)
 => (IORef (Repr (DynIO k)) -> Eval (DynIO k))
 -> Eval (DynIO k)
 -> Eval (DynIO k)
newMut mkRef ev' = liftA2 (S.#) ev' (field (S.self_ "run") ev)
  where
    ev = do
      se <- asks (getSelf . snd)
      r <- ask
      (return
        . Repr
        . Block
        . const
        . dynIO)
        (do
          ref <- newIORef (se S.# "val")
          (runDynIO . self) (runReader (f (mkRef ref)) r))
      where
        f
         :: (S.Self k, Ord k)
         => Eval (DynIO k) -> Eval (DynIO k)
        f ev =
          liftA2 (S.#) (asks (getSelf . snd)) ev
            <&> (S.#. "onSuccess")
  
  
makeRef
 :: (S.Self k, Ord k)
 => Eval (DynIO k)
 -> Synt (Res k) (IORef (Repr (DynIO k)) -> Eval (DynIO k))
makeRef ev' = makeBlock
  [ S.self_ "set" S.#= runs setMut
  , S.self_ "get" S.#= runs getMut
  ] 
  where
    runs f = Synt 
      (readSynt (makeBlock [ S.self_ "run" S.#= Synt (pure f) ])
        <&> (\ f ref -> liftA2 (S.#) ev' (f ref)))
  
    setMut
      :: (S.Self k, Ord k)
      => IORef (Repr (DynIO k))
      -> Eval (DynIO k)
    setMut ref = do
      se <- asks (getSelf . snd)
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
      -> Eval (DynIO k)
    getMut ref = reader (\ r ->
      (Repr
        . Block
        . const
        . dynIO)
        (do 
          v <- readIORef ref
          (runDynIO . self) (runReader (f (pure v)) r)))
      where
        f 
         :: (S.Self k, Ord k)
         => Eval (DynIO k) -> Eval (DynIO k)
        f ev =
          liftA2 (S.#) 
            (asks (getSelf . snd))
            (field (S.self_ "val") ev)
            <&> (S.#. "onSuccess")
  