{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveFoldable #-}

module My.Eval.IO
  (evalIO, io, ioMode, runDynIO, DynIO, dynIO)
  where

import My.Types.DynMap
import My.Types.Error
import My.Types.Eval
import My.Types.Paths.Tup
import qualified My.Types.Syntax.Class as S
import My.Util ((<&>), Compose(..))
import Control.Applicative (liftA2, (<|>))
import Data.IORef
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Data.Semigroup (Option(..), Last(..))
import System.IO hiding (openFile)

import Debug.Trace


evalIO
  :: (S.Self k, Ord k)
  => Res k (Eval (DynIO k))
  -> ([StaticError k], IO (Maybe (DynError k)))
evalIO m = liftA2
  (\ ev en -> runDynIO (self (ev en r0)))
  (runRes m ["io", "ioMode"])
  (runRes imports [])
  where
    imports = traverse (fmap (\ ev -> ev [] r0)) [io, ioMode]
    
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


io :: (S.Self k, Ord k) => Res k (Eval (DynIO k))
io = do 
  eva <- async
  mkH <- makeHandle eva
  mkR <- makeRef eva
  S.tup_
    [ S.self_ "openFile" S.#: (openFile mkH <&> (`id` eva))
    , S.self_ "stdout" S.#: pure (mkH stdout)
    , S.self_ "stdin" S.#: pure (mkH stdin)
    , S.self_ "stderr" S.#: pure (mkH stderr)
    , S.self_ "newMut" S.#: pure (newMut mkR eva)
    ]
  where
    async = S.tup_
      [ S.self_ "onSuccess" S.#: S.tup_ []
      , S.self_ "onError" S.#: S.tup_ []
      ]

ioMode :: (S.Self k, Ord k) => Res k (Eval (DynIO k))
ioMode = S.tup_
  [ S.self_ "read" S.#: S.block_
      [ S.self_ "match" S.#= S.self_ "ifRead" ]
  , S.self_ "write" S.#: S.block_
      [ S.self_ "match" S.#= S.self_ "ifWrite" ]
  , S.self_ "append" S.#: S.block_
      [ S.self_ "match" S.#= S.self_ "ifAppend" ]
  , S.self_ "readWrite" S.#: S.block_
      [ S.self_ "match" S.#= S.self_ "ifReadWrite" ]
  ]

    
openFile
  :: forall k. (S.Self k, Ord k)
  => (Handle -> Eval (DynIO k))
  -> Res k (Eval (DynIO k) -> Eval (DynIO k))
openFile mkHandle = run <&> (\ ev ev' en se ->
  ev' en se S.# ev en se)
  where
    run :: Res k (Eval (DynIO k))
    run = S.block_
      [ S.self_ "run" S.#=
          S.self_ "mode" S.# S.tup_
            [ S.self_ "ifRead" S.#:
              pure (open ReadMode)
            , S.self_ "ifWrite" S.#:
              pure (open WriteMode)
            , S.self_ "ifAppend" S.#:
              pure (open AppendMode)
            , S.self_ "ifReadWrite" S.#:
              pure (open ReadWriteMode)
            ] S.#. "match"
      ]
      
    open
      :: (S.Self k, Ord k) => IOMode -> Eval (DynIO k)
    open mode en se = strk (self (se S.#. "file"))
      (\ t -> (Repr
        . Block
        . const
        . dynIO
        . withFile (T.unpack t) mode)
        (\ h -> (runDynIO . self) (se
          S.# mkHandle h en se
          S.#. "onSuccess")))

          
makeBlock
  :: (Ord k, Applicative f)
  => [Tup k (Res k (a -> Eval (Dyn k f)))]
  -> Res k (a -> Eval (Dyn k f))
makeBlock ts = (dynCheckTup . foldMap (Comps . getTup)) ts
  <&> (\ kv a en se -> (Repr . Block) (\ se ->
    (fmap (\ f -> f a en se)
      . dyn) (DynMap Nothing kv)))

makeHandle
  :: (S.Self k, Ord k)
  => Eval (DynIO k)
  -> Res k (Handle -> Eval (DynIO k))
makeHandle ev' = makeBlock
  [ S.self_ "getLine" S.#: runs hGetLine
  , S.self_ "getContents" S.#: runs hGetContents
  , S.self_ "putText" S.#: runs hPutStr
  ]
  where
    runs f = makeBlock [ S.self_ "run" S.#: pure f ] 
      <&> (\ f h en se -> ev' en se S.# f h en se)
  
    hGetLine
      :: (S.Self k, Ord k) => Handle -> Eval (DynIO k)
    hGetLine h en se = (Repr . Block . const . dynIO) (do
      t <- T.hGetLine h
      (runDynIO . self) (se
        S.# field (S.self_ "text") (\ _ _ -> Repr (Text t)) en se
        S.#. "onSuccess"))
      
    hGetContents
      :: (S.Self k, Ord k) => Handle -> Eval (DynIO k)
    hGetContents h en se = (Repr . Block . const . dynIO) (do
      t <- T.hGetContents h
      (runDynIO . self) (se
        S.# field (S.self_ "text") (\ _ _ -> Repr (Text t)) en se
        S.#. "onSuccess"))
  
    hPutStr
      :: (S.Self k, Ord k) => Handle -> Eval (DynIO k)
    hPutStr h _ se = strk (self (se S.#. "text")) (\ t ->
      (Repr
      . Block
      . const 
      . dynIO)
        (T.hPutStr h t
          >> (runDynIO . self) (se S.#. "onSuccess")))
      
      
field :: k -> Eval (DynIO k) -> Eval (DynIO k)
field k ev en _ = (Repr . Block) (\ se ->
  (dyn
  . DynMap Nothing
  . M.singleton k . pure) (ev en se))
      
      
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
  => (IORef (Repr (DynIO k)) -> Eval (DynIO k))
  -> Eval (DynIO k)
  -> Eval (DynIO k)
newMut mkRef ev' en se = ev' en se
  S.# field (S.self_ "run") ev en se
  where
    ev en se = (Repr . Block . const . dynIO) (do
      ref <- newIORef (se S.# "val")
      (runDynIO . self)
        (se
          S.# mkRef ref en se
          S.#. "onSuccess"))
  
  
makeRef
  :: (S.Self k, Ord k)
  => Eval (DynIO k)
  -> Res k (IORef (Repr (DynIO k)) -> Eval (DynIO k))
makeRef ev' = makeBlock
  [ S.self_ "set" S.#: runs setMut
  , S.self_ "get" S.#: runs getMut
  ] 
  where
    runs f = makeBlock [ S.self_ "run" S.#: pure f ]
      <&> (\ f ref en se -> ev' en se S.# f ref en se)
  
    setMut
      :: (S.Self k, Ord k)
      => IORef (Repr (DynIO k))
      -> Eval (DynIO k)
    setMut ref en se = 
      (Repr
      . Block
      . const
      . dynIO)
        (writeIORef ref (se S.#. "val")
          >> (runDynIO . self) (se S.#. "onSuccess"))
          
    getMut
      :: (S.Self k, Ord k)
      => IORef (Repr (DynIO k))
      -> Eval (DynIO k)
    getMut ref en se = (Repr
      . Block
      . const
      . dynIO)
        (do 
          v <- readIORef ref
          (runDynIO . self)
            (se 
              S.# field (S.self_ "val") (\ _ _ -> v) en se
              S.#. "onSuccess"))
  