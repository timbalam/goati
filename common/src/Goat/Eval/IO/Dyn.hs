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
  :: (S.IsString k, Ord k)
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
 :: (S.IsString k, Ord k) => Synt (Res k) (Eval (DynIO k))
io = Synt (do 
  eva <- readSynt async
  mkH <- readSynt (makeHandle eva)
  mkR <- readSynt (makeRef eva)
  readSynt (S.block_
    [ "" S.#. "openFile" S.#=
        Synt (readSynt (openFile mkH) <&> (`id` eva))
    , "" S.#. "stdout" S.#= Synt (pure (mkH stdout))
    , "" S.#. "stdin" S.#= Synt (pure (mkH stdin))
    , "" S.#. "stderr" S.#= Synt (pure (mkH stderr))
    , "" S.#. "newMut" S.#= Synt (pure (newMut mkR eva))
    ]))
  where
    async = S.block_
      [ "" S.#. "onSuccess" S.#= S.block_ []
      , "" S.#. "onError" S.#= S.block_ []
      ]

ioMode
 :: (S.IsString k, Ord k) => Synt (Res k) (Eval (DynIO k))
ioMode = S.block_
  [ "" S.#. "read" S.#= S.block_
      [ "" S.#. "match" S.#= "" S.#. "ifRead" ]
  , "" S.#. "write" S.#= S.block_
      [ "" S.#. "match" S.#= "" S.#. "ifWrite" ]
  , "" S.#. "append" S.#= S.block_
      [ "" S.#. "match" S.#= "" S.#. "ifAppend" ]
  , "" S.#. "readWrite" S.#= S.block_
      [ "" S.#. "match" S.#= "" S.#. "ifReadWrite" ]
  ]

    
openFile
 :: forall k
  . (S.IsString k, Ord k)
 => (Handle -> Eval (DynIO k))
 -> Synt (Res k) (Eval (DynIO k) -> Eval (DynIO k))
openFile mkHandle = Synt (readSynt run <&> liftA2 (S.#))
  where
    run :: Synt (Res k) (Eval (DynIO k))
    run = S.block_
      [ "" S.#. "run" S.#=
          "" S.#. "mode" S.# S.block_
            [ "" S.#. "ifRead" S.#=
              Synt (pure (open ReadMode))
            , "" S.#. "ifWrite" S.#=
              Synt (pure (open WriteMode))
            , "" S.#. "ifAppend" S.#=
              Synt (pure (open AppendMode))
            , "" S.#. "ifReadWrite" S.#=
              Synt (pure (open ReadWriteMode))
            ] S.#. "match"
      ]
      
    open
      :: (S.IsString k, Ord k) => IOMode -> Eval (DynIO k)
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
           :: (S.IsString k, Ord k)
           => Eval (DynIO k) -> Eval (DynIO k)
          f ev =
            liftA2 (S.#)
              (asks (getSelf . snd))
              ev
              <&> (S.#. "onSuccess")

          
makeBlock
 :: (S.IsString k, Ord k, Applicative f, Foldable f)
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
 :: (S.IsString k, Ord k)
 => Eval (DynIO k)
 -> Synt (Res k) (Handle -> Eval (DynIO k))
makeHandle ev' = makeBlock
  [ "" S.#. "getLine" S.#= runs hGetLine
  , "" S.#. "getContents" S.#= runs hGetContents
  , "" S.#. "putText" S.#= runs hPutStr
  ]
  where
    runs f = Synt
      (readSynt (makeBlock [ "" S.#. "run" S.#= Synt (pure f) ])
        <&> (\ f' h -> liftA2 (S.#) ev' (f' h)))
  
    hGetLine
      :: (S.IsString k, Ord k) => Handle -> Eval (DynIO k)
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
           :: (S.IsString k, Ord k)
           => Eval (DynIO k) -> Eval (DynIO k)
          f ev =
            liftA2 (S.#)
              (asks (getSelf . snd))
              (field (S.fromString "text") ev)
              <&> (S.#. "onSuccess")
            
      
    hGetContents
     :: (S.IsString k, Ord k) => Handle -> Eval (DynIO k)
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
          f :: (S.IsString k, Ord k)
            => Eval (DynIO k) -> Eval (DynIO k)
          f ev =
            liftA2 (S.#)
              (asks (getSelf . snd))
              (field (S.fromString "text") ev)
              <&> (S.#. "onSuccess")
                
  
    hPutStr
     :: (S.IsString k, Ord k)
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
 :: (S.IsString k, Ord k)
 => (IORef (Repr (DynIO k)) -> Eval (DynIO k))
 -> Eval (DynIO k)
 -> Eval (DynIO k)
newMut mkRef ev' = liftA2 (S.#) ev' (field (S.fromString "run") ev)
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
          ref <- newIORef (se S.#. "val")
          (runDynIO . self) (runReader (f (mkRef ref)) r))
      where
        f
         :: (S.IsString k, Ord k)
         => Eval (DynIO k) -> Eval (DynIO k)
        f ev =
          liftA2 (S.#) (asks (getSelf . snd)) ev
            <&> (S.#. "onSuccess")
  
  
makeRef
 :: (S.IsString k, Ord k)
 => Eval (DynIO k)
 -> Synt (Res k) (IORef (Repr (DynIO k)) -> Eval (DynIO k))
makeRef ev' = makeBlock
  [ "" S.#. "set" S.#= runs setMut
  , "" S.#. "get" S.#= runs getMut
  ] 
  where
    runs f = Synt 
      (readSynt (makeBlock [ "" S.#. "run" S.#= Synt (pure f) ])
        <&> (\ f ref -> liftA2 (S.#) ev' (f ref)))
  
    setMut
      :: (S.IsString k, Ord k)
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
      :: (S.IsString k, Ord k)
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
         :: (S.IsString k, Ord k)
         => Eval (DynIO k) -> Eval (DynIO k)
        f ev =
          liftA2 (S.#) 
            (asks (getSelf . snd))
            (field (S.fromString "val") ev)
            <&> (S.#. "onSuccess")
  