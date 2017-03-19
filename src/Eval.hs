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


type IOExcept = Except (Ided IO)
type Eval = Except (Ided (StateT EvalNode (ContT EvalNode IO)))
data EvalNode = EvalNode (Node (Eval Value))
    
evalName :: T.Name T.Rval -> Eval (T.Name Value)
evalName (T.Key r) = fmap T.Key $ evalRval r
evalName (T.Ref x) = return . return . return $ T.Ref x


evalRval :: T.Rval -> (Eval Value -> EvalNode -> EvalNode) -> EvalNode -> EvalNode
evalRval (T.Number x) = \ c -> c (return (Number x))
evalRval (T.String x) = \ c -> c (return (String x))
evalRval (T.Rident x) = lookupNode (EnvKey x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> (Eval Value -> EvalNode -> EvalNode) -> EvalNode -> EvalNode
    evalRoute (T.Route r x) = liftA2 viewValueWithKey (evalName x) (evalRval r)
    evalRoute (T.Atom x) = \ c -> evalName x (\ k -> lookupNode (SelfKey k) c)

evalRval (T.Rnode []) = \ c -> c newSymbol
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
 
evalLaddr :: T.Laddress -> (Eval LSetter -> EvalNode -> EvalNode) -> EvalNode -> EvalNode
evalLaddr (T.Lident x) = \ c -> c (return (alterNode (EnvKey x)))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> (Eval LSetter -> EvalNode -> EvalNode) -> EvalNode -> EvalNode
    evalLroute (T.Route l key) =
      (\ c -> evalName key
      (\ kr -> evalLaddr l
      (\ lsetr -> c (do{ k <- kr; lset <- lsetr; return (overOrNewValueWithKey k . lset) })
      )))
    evalLroute (T.Atom key) =
      (\ c -> evalName key
      (\ kr -> c (do{ k <- kr; return (alterNode (SelfKey k)) })
      ))
    
    
unsetNodeWithKey :: T.Name Value -> EvalNode -> EvalNode
unsetNodeWithKey k node = insertNode (SelfKey k) (throwUnboundVar k)

    
unsetValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetValueWithKey k = ap newNode . fmap (unsetNodeWithKey k . unNode)
    
    
unsetOrEmptyValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetOrEmptyValueWithKey k = ap newNode . fmap (unsetNodeWithKey k) . unNodeOrEmpty

    
evalStmt :: T.Stmt -> EvalNode -> EvalNode
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> EvalNode -> EvalNode
    evalUnassign (T.Lident x) = insertNode (EnvKey k) (throwUnboundVar k)
    evalUnassign (T.Lroute r) = evalUnassignRoute r
    
    
    evalUnassignRoute :: T.Route T.Laddress -> EvalNode -> EvalNode
    evalUnassignRoute (T.Route l x) =
      evalName x
      (\ kr -> evalLaddr l
      (\ lsetr -> do{ k <- kr; lset <- lsetr; return (lset (unsetOrEmptyValueWithKey k)) }
      ))
    evalUnassignRoute (T.Atom x) =
      evalName x
      (\ kr -> do{ k <- kr; return 
        ; return (toNodeList (do{ k <- kr; return (\ scope -> scope { cobj = deleteVtable k (cobj scope) }) }))
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
    
    
evalPlainRoute :: T.PlainRoute -> Eval (Getter (IOClasses Scope Value) (IOClasses Scope Value), Setter' (IOClasses Scope Value) (IOClasses Scope Value))
evalPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kr <- evalName key
    ; vset <- overValueWithKey kr
    ; return $ (viewValueWithKey kr, vset)
    }
evalPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kr <- evalName key
    ; (lget, lset) <- evalPlainRoute l 
    ; vset <- overValueWithKey kr
    ; return (lget . viewValueWithKey kr, lset . vset)
    }

    
splitPlainRoute :: T.PlainRoute -> Eval (IOClasses Scope Value -> (IOClasses Scope Value, IOClasses Scope Value))
splitPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kr <- evalName key
    ; vunset <- unsetValueWithKey kr
    ; return (\ vr -> (viewValueWithKey kr vr, vunset vr))
    }
splitPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kr <- evalName key
    ; vunset <- unsetValueWithKey kr
    ; (lget, lset) <- evalPlainRoute l
    ; return (\ vr -> (lget (viewValueWithKey kr vr), lset vunset vr))
    }
    

evalAssign :: T.Lval -> Eval (IOClasses Scope Value -> IONodeList Scope)
evalAssign (T.Laddress x) = 
  do{ lsetr <- evalLaddr x
    ; return (\ vr -> toNodeList (lsetr <*> pure (const vr)))
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
    evalReversibleStmt :: T.ReversibleStmt -> Eval (State (IOClasses Scope Value) (IONodeList Scope))
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      do{ lassign <- evalAssign l 
        ; vsplit <- splitPlainRoute keyroute
        ; return (do{ wr <- state vsplit; return (lassign wr) })
        }
    evalReversibleStmt _ = return (return emptyNodeList)
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> State (IOClasses Scope Value) (IONodeList Scope) -> Eval (IOClasses Scope Value -> IONodeList Scope)
    unpackLval l unpack =
      do{ lassign <- evalAssign l
        ; return (\ vr -> let (node, vr') = runState unpack vr in node `mergeNodeList` lassign vr)
        }
        