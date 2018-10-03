{-# LANGUAGE OverloadedStrings #-}

module My.Eval.IO
  where

import My.Types.Eval
import System.IO (IOMode(..))
import qualified Data.Map as M


type DynIO k = Dyn k ((,) (Alt IO ()))

dynIO :: IO () -> DynIO k a
dynIO io = (Compose
  . (,) (Alt io)
  . Compose)
    (DynMap Nothing M.empty)
    
runDynIO :: Self (DynIO k) -> IO ()
runDynIO (Block (Compose (io, _))) = io
runDynIO _                         = pure ()


io :: S.Self k => Res k (Eval (DynIO k))
io = do 
  mkH <- makeHandle
  tuple_
    [ S.self_ "openFile" S.#= openFile mkHandle
    , S.self_ "stdout" S.#= pure (mkHandle stdout),
    , S.self_ "stdin" S.#= pure (mkHandle stdin),
    , S.self_ "stderr" S.#= pure (mkHandle stderr),
    , S.self_ "mut" S.#= mut
    ]
    
ioMode :: S.Self k => Res k (Eval (DynIO k))
ioMode = tuple_
  [ S.self_ "read" S.#: match (S.self_ "ifRead")
  , S.self_ "write" S.#: match (S.self_ "ifWrite")
  , S.self_ "append" S.#: match (S.self_ "ifAppend")
  , S.self_ "readWrite" S.#: match (S.self_ "ifReadWrite")
  ]
  where
    match :: Res k (Eval (DynIO k)) -> Res k (Eval (DynIO k))
    match v = block_ [ S.self_ "match" S.#= v ] 

    
openFile
  :: S.Self k
  => (Handle -> Eval (DynIO k))
  -> Res k (Eval (DynIO k))
openFile mkHandle = run where

  run :: Res k (Eval (Dyn IO k))
  run = (S.self_ "ioMode") S.# S.tuple_
      [ S.self_ "ifRead" S.#:
        pure (open ReadMode (S.self_ "file"))
      , S.self_ "ifWrite" S.#:
        pure (open WriteMode (S.self_ "file"))
      , S.self_ "ifAppend" S.#:
        pure (open AppendMode (S.self_ "file"))
      , S.self_ "ifReadWrite" S.#:
        pure (open ReadWriteMode (S.self_ "file"))
      ] S.#. "match"
  
  open
    :: S.Self k
    => IOMode
    -> Eval (DynIO k)
    -> Eval (DynIO k)
  open mode ev en se = strk (ev en se)
    (\ t -> (Repr
      . Block
      . const
      . dynIO
      . withFile (toString t) mode)
      (\ h -> (runDynIO . self) (se
        S.# field (S.self_ "handle") (mkHandle h en se)
        S.#. "onSuccess")))


makeHandle :: S.Self k => Res (Handle -> Eval (DynIO k))
makeHandle = dynCheckTup (foldMap (Comps . getTup)
  [ S.self_ "getLine" S.#: pure hGetLine
  , S.self_ "getContents" S.#: pure hGetContents
  , S.self_ "putStr" S.#: pure (`hPutStr` S.self_ "text")
  ]) <&> (\ kv h en se ->
    (Repr
    . Block
    . const
    . fmap (\ f en se -> f h en se)
    . dyn)
      (DynMap Nothing kv))
  where
    
  
    hGetLine :: S.Self k => Handle -> Eval (DynIO k)
    hGetLine h _ se = (Repr . Block . const . dynIO) (do
      t <- T.hGetLine h
      (runDynIO . self) (se
        S.# field (S.Self_ "text") (Repr (Text t))
        S.#. "onSuccess"))
      
    hGetContents :: S.Self k => Handle -> Eval (DynIO k)
    hGetContents h _ se = (Repr . Block . const . dynIO) (do
      t <- T.hGetContents h
      (runDynIO . self) (se
        S.# field (S.self_ "text") (Repr (Text t))
        S.# "onSuccess"))
  
    hPutStr :: Handle -> Eval (DynIO k) -> Eval (DynIO k)
    hPutStr h ev en se = strk (ev en se) (\ t ->
      (Repr 
      . Block
      . const 
      . dynIO)
        (T.hPutStr h t
          >> (runDynIO . self) (se S.# "onSuccess")))
      
      
field :: k -> Repr (DynIO k) -> Repr (DynIO k)
field k v = (Repr
  . Block
  . const
  . dyn
  . DynMap Nothing)
  (M.singleton k v)
      
      
strk 
  :: Repr (DynIO k)
  -> (Text -> Repr (DynIO k))
  -> Repr (DynIO k)
strk (Repr (Text t)) k = k t
strk _               _ = typee NotText where
  typee = Block . const . throwDyn . TypeError
  


mut :: S.Self k => Repr (DynIO k)
mut = (Repr . Block) (\ se -> dynIO (do
  ref <- newIORef (se S.# "val")
  (runDynIO . self)
    (se S.# field (S.self_ "ref") (mkRef ref) S.#. "onSuccess")))
  


  NewMut -> (pure . iotry)
    (do
      err <- newIORef (e `At` Key "val")
      ok (iorefSelf err))
    
  GetMut ref -> (pure . iotry)
    (do
      v <- readIORef ref
      ok ((M.singleton (Key "val") . lift) (absurd <$> v)))
  
  SetMut ref -> (pure . iotry)
    (writeIORef ref (e `At` Key "val") >> ok M.empty) 


    iorefSelf :: IORef (Repr K Void) -> M.Map K (Scope K (Repr K) a)
    iorefSelf x = M.fromList [
      (Key "set", member (SetMut x)),
      (Key "get", member (GetMut x))
      ]
      where member = lift . wrapIOPrim    

  