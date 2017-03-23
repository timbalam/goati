{-# LANGUAGE FlexibleContexts #-}

module Eval
  ( evalRval
  )
where
import Control.Monad.Except
  ( throwError
  , catchError
  , MonadError
  )
import Control.Monad.State
  ( runStateT
  , evalStateT
  , execStateT
  , runState
  , evalState
  , execState
  , state
  , get
  , put
  )
import Control.Monad.IO.Class( liftIO )
import Control.Monad.Trans.Reader
  ( ReaderT
  , runReaderT
  , mapReaderT
  , ask
  , local
  )
import Control.Monad.Identity
  ( Identity(Identity)
  , runIdentity
  )
import Control.Monad.Trans.Class( lift )
import Control.Applicative
  ( (<|>)
  , liftA2
  )
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Getter s a = s -> a
type Setter s t a b = (a -> b) -> s -> t
type Setter' s a = Setter s s a a


view_1 :: Getter (a, b) a
view_1 = fst


over_1 :: Setter (a, b) (c, b) a c
over_1 f (a, b) = (f a, b)


view_2 :: Getter (a, b) b
view_2 = snd


over_2 :: Setter (a, b) (a, c) b c
over_2 f (a, b) = (a, f b)


lookupValue :: T.Name Value -> Value -> IOExcept Value
lookupValue k v =
  do{ self <- execNode (unNode v)
    ; runClasses (lookupClassesWith k unSelf) self
    }


type EvalScope = Scope (Eval Value)



    
evalName :: T.Name T.Rval -> (Eval (T.Name Value) -> EvalScope -> EvalScope) -> EvalScope -> EvalScope
evalName (T.Key r) = T.Key <$> evalRval r
evalName (T.Ref x) = return (T.Ref x)


evalRval :: T.Rval -> Eval Value
evalRval (T.Number x) = return (Number x)
evalRval (T.String x) = return (String x)
evalRval (T.Rident x) = evalEnv (lookupNodeM x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval Value
    evalRoute (T.Route r x) = liftA2 viewValueWithKey (evalName x) (evalRval r)
    evalRoute (T.Atom x) =
      do{ k <- evalName x
        ; eval (lookupNodeM k)
        }

evalRval (T.Rnode []) = newSymbol
evalRval (T.Rnode stmts) =
  do{ nn <- newNode
    ; nodes <- mapM evalStmt stmts
    ; let node = foldr mergeNodeList emptyNodeList nodes
    ; return
        (do{ scope <- ask
           ; let par = penv scope `concatVtable` (withVtable (const scope)) cenv scope
                 node' = execScope node (Scope { penv = par, cenv = emptyVtable, cobj = emptyVtable, self = emptyVtable })
           ; return nn $ node'
           })
    }
evalRval (T.App x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; nn <- newNode
    ; let app v w = nn (unNode w `concatNode` unNode v)
    ; return $ liftClasses2 app vf wf
    }
evalRval (T.Unop sym x) =
  do{ vr <- evalRval x
    ; return (do { v <- vr; liftClasses (evalUnop sym v) })
    }
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupValue` x
evalRval (T.Binop sym x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; return $
        do{ mv <- liftClasses2 (evalBinop sym) vr wr
          ; liftClasses mv
          }
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y =
      do{ opNode <- unNode <$> T.Key (binopSymbol sym) `lookupValue` x
        ; let opNode' = overNodeWithKey (T.Key rhsSymbol) (const $ return y) opNode
        ; self <- execNode opNode'
        ; runClasses (lookupSelf (T.Key resultSymbol)) self
        }
evalRval (T.Import x) = evalRval x


overNodeWithKey :: T.Name Value -> (v -> v) -> Node v -> Node v
overNodeWithKey k f = alterNode (SelfKey k) f
  
  
unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return mempty)


overValueWithKey :: T.Name Value -> (Eval Value -> Eval Value) -> Eval Value -> Eval Value
overValueWithKey k f = ap newNode . fmap (overNodeWithKey k f . unNode)
    
    
overOrNewValueWithKey :: T.Name Value -> (Eval Value -> Eval Value) -> Eval Value -> Eval Value
overOrNewValueWithKey k f = ap newNode . fmap (overNodeWithKey k f) . unNodeOrEmpty


type LSetter = Setter' EvalNode (Eval Value)
 
evalLaddr :: T.Laddress -> Eval LSetter
evalLaddr (T.Lident x) = return (\ f n -> n { env = alterNode x f (env n) })
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> (Eval LSetter -> EvalNode -> EvalNode) -> EvalNode -> EvalNode
    evalLroute (T.Route l key) =
      do{ k <- evalName key
        ; lset <- evalLaddr l
        ; return (overOrNewValue k . lset)
        }
    evalLroute (T.Atom key) =
      do{ k <- evalName key
        ; return (\ f n -> n { self = alterNode k f (self n) })
        }
    
    
unsetNodeWithKey :: T.Name Value -> EvalNode -> EvalNode
unsetNodeWithKey k n = n { self = insertNode k (throwUnboundVar k) (self n) }

    
unsetValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetValueWithKey k = ap newNode . fmap (unsetNodeWithKey k . unNode)
    
    
unsetOrEmptyValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetOrEmptyValueWithKey k = ap newNode . fmap (unsetNodeWithKey k) . unNodeOrEmpty

    
evalStmt :: T.Stmt -> Eval (EvalNode -> EvalNode)
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval (EvalNode -> EvalNode)
    evalUnassign (T.Lident x) = return (\ n -> n { env = insertNode k (throwUnboundVar k) (env n) })
    evalUnassign (T.Lroute r) = evalUnassignRoute r
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval (EvalNode -> EvalNode)
    evalUnassignRoute (T.Route l key) =
      do{ k <- evalName key
        ; lset <- evalLaddr l
        ; return (lset (unsetOrEmptyValueWithKey k))
        }
    evalUnassignRoute (T.Atom key) =
      do{ k <- evalName key
        ; return (insertNode (SelfKey k) (throwUnboundVar k)
        }
evalStmt (T.Assign l r) =
  do{ lassign <- evalAssign l
    ; vr <- evalRval r
    ; return (lassign <*> vr)
    }
evalStmt (T.Unpack r) =
  do{ vr <- evalRval r
    ; let selfr =
           (do{ v <- vr
              ; lift (execNode (unNode v))
              })
    ; return (toNodeList (return (\ scope -> scope { unpack = liftClasses2 mappend (unpack scope) selfr })))
    }
evalStmt (T.Eval r) =
  do{ vr <- evalRval r
    ; let run = 
            do{ v <- vr
              ; lift (execNode (unNode v)))
              }
    ; return (toNodeList (run >> return (const mempty)))
    }
    
    
evalPlainRoute :: T.PlainRoute -> Eval (Eval Value -> Eval Value, (Eval Value -> Eval Value) -> Eval Value -> Eval Value)
evalPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ k <- evalName key
    ; return (viewValueWithKey k, overValueWithKey k)
    }
evalPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ k <- evalName key
    ; (lget, lset) <- evalPlainRoute l 
    ; return (lget . viewValueWithKey k, lset . overValueWithKey k)
    }

    
splitPlainRoute :: T.PlainRoute -> Eval (Eval Value -> (Eval Value, Eval Value))
splitPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ k <- evalName key
    ; return (\ vr -> (viewValueWithKey k vr, unsetWithKey k vr))
    }
splitPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ k <- evalName key
    ; (lget, lset) <- evalPlainRoute l
    ; return (\ vr -> (lget (viewValueWithKey k vr), lset (unsetValueWithKey k vr)))
    }
    

evalAssign :: T.Lval -> Eval (Eval Value -> EvalNode -> EvalNode)
evalAssign (T.Laddress l) = 
  do{ lset <- evalLaddr l
    ; return (\ v -> lset (const v))
    }
evalAssign (T.Lnode xs) =
  do{ unpacks <- mapM evalReversibleStmt xs
    ; let unpack = foldr mergeNodeList emptyNodeList <$> sequence (unpacks)
    ; maybe
        (return (fst . runState unpack))
        (flip unpackLval unpack)
        (foldr (<|>) Nothing (map collectUnpackStmt xs))
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval (State (Eval Value) (EvalNode -> EvalNode))
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      do{ lassign <- evalAssign l 
        ; vsplit <- splitPlainRoute keyroute
        ; return (do{ wr <- state vsplit; return (lassign wr) })
        }
    evalReversibleStmt _ = return (return id)
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> State (Eval Value) (EvalNode -> EvalNode) -> Eval (Eval Value -> EvalNode -> EvalNode)
    unpackLval l unpack =
      do{ lassign <- evalAssign l
        ; return (\ vr -> let (node, vr') = runState unpack vr in node `mergeNodeList` lassign vr)
        }
        