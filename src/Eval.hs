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

type Classed = ClassedT Eval
type Scope = ScopeT Eval
type Self = SelfT Eval
type Env = EnvT Eval


lookupValue :: T.Name Value -> Value -> Cont Classed (Eval Value)
lookupValue k v = cont (\ c n ->
  do{ self <- (unNode v) emptyTable
    ; lookupTable k `runCont` (\ c w _ -> c w n) self
    })


evalRval :: T.Rval -> Cont Scope (Cont Classed (Eval Value))
evalRval (T.Number x) = return (return (return (Number x)))
evalRval (T.String x) = return (return (return (String x)))
evalRval (T.Rident x) = lookupScope (EnvKey x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Cont Scope (Cont Classed (Eval Value))
    evalRoute (T.Route r (T.Key x)) =
      do{ mk <- evalRval x
        ; mv <- evalRval r
        ; return (do { k <- bindClassed mk
                     ; v <- bindClassed mv
                     ; lookupValue (T.Key k) v
                     })
        }
    evalRoute (T.Route r (T.Ref x)) =
      do{ mv <- evalRval r
        ; return (do { v <- bindClassed mv
                     ; lookupValue (T.Ref x) v
                     })
    evalRoute (T.Atom (T.Key x)) =
      do{ mk <- evalRval x
        ; return (do{ k <- bindClassed mk
                    ; lookupTable (T.Key k)
                    })
        }
    evalRoute (T.Atom (T.Ref x)) = return (lookupTable (T.Ref x))

evalRval (T.Rnode []) = return newSymbol
evalRval (T.Rnode stmts) =
  do{ w <- m
    ; let (_, Bind n) = runWriter w
    ; return (do{ nn <- newNode; return (nn n) })
    }
  where
    (env, Bind n) = runWriter (foldr (\ a b -> b >>= evalStmt a) mempty stmts)
    -- m :: (Writer -> scope) -> scope
    m = M.foldrWithKey
      (\ k a b ->
         do{ v <- lookupTable k
           ; w <- b
           ; return (w >>= a v)
           })
      (return (writer (env, Bind n)))
      (pending env)
evalRval (T.App x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; return 
        (do{ v <- bindClassed vr
           ; w <- bindClassed wr
           ; return (do{ nn <- newNode; return (nn (unNode w . unNode v)) })
           })
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


unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return emptyNode)


overValueWithKey :: T.Name Value -> (Eval Value -> Eval Value) -> Eval Value -> Eval Value
overValueWithKey k f ev 
  do{ v <- ev
    ; nn <- newNode 
    ; return (nn (\ s -> unNode v s >>= alterTable k f)
    }


overOrNewValueWithKey :: T.Name Value -> (Eval Value -> Eval Value) -> Eval Value -> Eval Value
overOrNewValueWithKey k f ev =
  do{ n <- unNodeOrEmpty ev
    ; nn <- newNode
    ; return (nn (\ s -> n s >>= alterTable k f))
    }
    
    
evalLaddr :: T.Laddress -> (Cont Classed (Eval Value -> Eval Value)) -> Scope
-- alterTable x :: (Cont Classed (Eval Value) -> Cont Classed (Eval Value)) -> Scope
evalLaddr (T.Lident x) = alterTable x
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> (Cont Classed (Eval Value -> Eval Value)) -> Scope
    evalLroute (T.Route l (T.Key x)) fr = m `runCont` evalLaddr l
      where
        m :: Cont Scope (Cont Classed (Eval Value -> Eval Value))
        m =
          do{ kr <- evalRval x
            ; return
                (do{ k <- bindClassed kr
                   ; f <- fr
                   ; return (overOrNewValueWithKey (T.Key k) f)
                   })
            }
    evalLroute (T.Route l (T.Ref x)) fr = evalLaddr l fr'
      where
        fr' :: Cont Classed (Eval Value -> Eval Value)
        fr' =
          do{ f <- fr
            ; return (overOrNewValueWithKey (T.Ref x) f)
            }
    evalLroute (T.Atom (T.Key x)) fr = m `runCont` extract
      where
        m = 
          do{ kr <- evalRval x
            ; return ((do{ k <- bindClassed kr
                         ; f <- fr
                         ; return (alterTable (T.Key k) f)
                         }) `runCont` id)
            }
        extract n e = do{ tell (Bind n); return e }
    evalLroute (T.Atom (T.Ref x)) fr = extract n
      where
        k = T.Ref x
        n = (do{ f <- fr; return (alterTable (T.Ref x) f) }) `runCont` id
        extract n e = 
          do{ tell (Bind n)
            ; insertTable k (lookupTable k) e
            }
    
    
unsetValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetValueWithKey k ev =
  do{ v <- ev
    ; nn <- newNode
    ; return (nn (\ s -> unNode v s >>= flushTable k (throwUnboundVar k)))
    }
    
    
unsetOrEmptyValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetOrEmptyValueWithKey k ev =
  do{ n <- unNodeOrEmpty ev
    ; nn <- newNode
    ; return (nn (\ s -> n s >>= flushTable k (throwUnboundVar)))
    }
    
evalStmt :: T.Stmt -> Scope
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Scope
    evalUnassign (T.Lident x) = flushTable x (throwUnboundVar x)
    evalUnassign (T.Lroute r) = evalUnassignRoute r
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Scope
    evalUnassignRoute (T.Route l (T.Key x)) = m `runCont` evalLaddr l
      where
        m = 
          do{ kr <- evalRval x
            ; return (do{ k <- kr; return (unsetOrEmptyValueWithKey k) })
            }
    evalUnassignRoute (T.Route l (T.Ref x)) = evalLaddr l fr
      where
        fr = return (unsetOrEmptyValueWithKey (T.Ref x))
    evalUnassignRoute (T.Atom (T.Key x)) = m `runCont` extract
      where
        m =
          do{ kr <- evalRval x
            ; return 
                ((do{ k <- bindClassed kr
                    ; return (flushTable (T.Key k) (throwUnboundVar (T.Key k)))
                    }) `runCont` id)
            }
        extract n e = do{ tell (Bind n); return e }
    evalUnassignRoute (T.Atom (T.Ref x)) = extract n
      where
        k = T.Ref x
        n = flushTable k (throwUnboundVar k)
        extract n e =
          do{ tell (Bind n)
            ; return (insertTable k (lookupTable k) e)
            }
evalStmt (T.Assign l r) = evalRval r `runCont` evalAssign l
evalStmt (T.Unpack r) = m `runCont` extract
  where
    extract n e =
      do{ x <- n emptyTable
        ; x `concatTable`
        }
    m = 
      do{ vr <- evalRval r
        ; return
            ((do{ v <- bindClassed vr
                ; return (unNode v)
                }) `runCont` id)
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
    

evalAssign :: T.Lval -> Cont Classed (Eval Value) -> Scope
evalAssign (T.Laddress l) = evalLaddr l . fmap const
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
        