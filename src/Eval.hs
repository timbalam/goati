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
  , State
  )
import Control.Monad.IO.Class( liftIO )
import Control.Monad.Trans.Reader
  ( ReaderT
  , runReaderT
  , mapReaderT
  , ask
  , local
  )
import Control.Monad.Writer
  ( writer
  , Writer
  , runWriter
  , censor
  , tell
  )
import Control.Monad.Cont
  ( Cont
  , cont
  , runCont
  , withCont
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
import Control.Monad( ap )
import Data.Monoid
  ( Alt(Alt)
  , getAlt
  )
import qualified Data.Map as M
 
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


lookupValue :: T.Name Value -> Value -> Eval Value
lookupValue k v =
  do{ self <- (unNode v) emptyTable
    ; x <- finaliseTable self
    ; lookupFinalised k x
    }


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
                     ; return (lookupValue (T.Key k) v)
                     })
        }
    evalRoute (T.Route r (T.Ref x)) =
      do{ mv <- evalRval r
        ; return (do { v <- bindClassed mv
                     ; return (lookupValue (T.Ref x) v)
                     })
        }
    evalRoute (T.Atom (T.Key x)) =
      do{ mk <- evalRval x
        ; return (do{ k <- bindClassed mk
                    ; lookupTable (T.Key k)
                    })
        }
    evalRoute (T.Atom (T.Ref x)) = return (lookupTable (T.Ref x))

evalRval (T.Rnode []) = return (return newSymbol)
evalRval (T.Rnode stmts) =
  do{ wr <- m
    ; return
        (do{ w <- wr
           ; let (_, Bind n') = runWriter w
           ; return (do{ nn <- newNode; return (nn n') })
           })
    }
  where
    (env, Bind n) = runWriter (foldr (\ a b -> b >>= evalStmt a) (return emptyTable) stmts)
    -- m :: (Writer -> scope) -> scope
    m = M.foldrWithKey
      (\ k a b ->
         do{ vr <- lookupTable k
           ; wr <- b
           ; return
               (do{ v <- vr
                  ; w <- wr
                  ; return
                      (do{ e <- w
                         ; a (return v) e
                         })
                  })
           })
      (return (return (writer (env, Bind n))))
      (pending env)
evalRval (T.App x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; return 
        (do{ v <- bindClassed vr
           ; w <- bindClassed wr
           ; return (do{ nn <- newNode; return (nn (\ x -> unNode w x >>= unNode v)) })
           })
    }
evalRval (T.Unop sym x) =
  do{ vr <- evalRval x
    ; return
        (do { v <- bindClassed vr
            ; return (evalUnop sym v)
            })
    }
  where
    evalUnop :: T.Unop -> Value -> Eval Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupValue` x
evalRval (T.Binop sym x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; return 
        (do{ v <- bindClassed vr
           ; w <- bindClassed wr
           ; return (evalBinop sym v w)
           })
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> Eval Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y =
      do{ op <- T.Key (binopSymbol sym) `lookupValue` x
        ; xop <- unNode op emptyTable
        ; xop' <- insertTable (T.Key rhsSymbol) (return y) xop
        ; self <- finaliseTable xop'
        ; lookupFinalised (T.Key resultSymbol) self
        }
evalRval (T.Import x) = evalRval x


unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return emptyNode)

overValueWithKey :: T.Name Value -> (Eval Value -> Eval Value) -> Eval Value -> Eval Value
overValueWithKey k f ev =
  do{ v <- ev
    ; nn <- newNode 
    ; return (nn (\ s -> unNode v s >>= alterTable k f))
    }


overOrNewValueWithKey :: T.Name Value -> (Eval Value -> Eval Value) -> Eval Value -> Eval Value
overOrNewValueWithKey k f ev =
  do{ n <- unNodeOrEmpty ev
    ; nn <- newNode
    ; return (nn (\ s -> n s >>= alterTable k f))
    }
    
    
evalLaddr :: T.Laddress -> Cont Classed (Eval Value -> Eval Value) -> Scope
-- alterTable x :: (Cont Classed (Eval Value) -> Cont Classed (Eval Value)) -> Scope
evalLaddr (T.Lident x) = alterTable x . ap
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
            ; insertTable x (lookupTable k) e
            }
    
    
unsetValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetValueWithKey k ev =
  do{ v <- ev
    ; nn <- newNode
    ; return (nn (\ s -> unNode v s >>= flushTable k))
    }
    
    
unsetOrEmptyValueWithKey :: T.Name Value -> Eval Value -> Eval Value
unsetOrEmptyValueWithKey k ev =
  do{ n <- unNodeOrEmpty ev
    ; nn <- newNode
    ; return (nn (\ s -> n s >>= flushTable k))
    }
    
evalStmt :: T.Stmt -> Scope
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Scope
    evalUnassign (T.Lident x) = flushTable x
    evalUnassign (T.Lroute r) = evalUnassignRoute r
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Scope
    evalUnassignRoute (T.Route l (T.Key x)) = m `runCont` evalLaddr l
      where
        m = 
          do{ kr <- evalRval x
            ; return (do{ k <- bindClassed kr; return (unsetOrEmptyValueWithKey (T.Key k)) })
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
                    ; return (flushTable (T.Key k))
                    }) `runCont` id)
            }
        extract n e = do{ tell (Bind n); return e }
    evalUnassignRoute (T.Atom (T.Ref x)) = extract n
      where
        k = T.Ref x
        n = flushTable k
        extract n e =
          do{ tell (Bind n)
            ; insertTable x (lookupTable k) e
            }
evalStmt (T.Assign l r) = evalRval r `runCont` evalAssign l
evalStmt (T.Unpack r) = m `runCont` extract
  where
    m = 
      do{ vr <- evalRval r
        ; return (bindClassed vr `runCont` unNode)
        }
    extract n e = do{ tell (Bind n); return e }
evalStmt (T.Eval r) = m `runCont` run
  where
    m =
      do{ vr <- evalRval r
        ; return (bindClassed vr `runCont` unNode)
        }
    run n e = do{ tell (Bind (\ x -> n x >> return x)); return e }
    

viewValueWithKey :: T.Name Value -> Eval Value -> Eval Value
viewValueWithKey k ev = ev >>= lookupValue k
    
    
evalPlainRoute :: T.PlainRoute -> Cont Scope (Cont Classed (Eval Value -> Eval Value, (Eval Value -> Eval Value) -> Eval Value -> Eval Value))
evalPlainRoute (T.PlainRoute (T.Atom (T.Key x))) =
  do{ kr <- evalRval x
    ; return
        (do{ k <- bindClassed kr
           ; return (viewValueWithKey (T.Key k), overValueWithKey (T.Key k))
           })
    }
evalPlainRoute (T.PlainRoute (T.Atom (T.Ref x))) =
  return (return (viewValueWithKey (T.Ref x), overValueWithKey (T.Ref x)))
evalPlainRoute (T.PlainRoute (T.Route l (T.Key x))) =
  do{ kr <- evalRval x
    ; lensr <- evalPlainRoute l
    ; return 
        (do{ k <- bindClassed kr
           ; (lget, lset) <- lensr
           ; return (lget . viewValueWithKey (T.Key k), lset . overValueWithKey (T.Key k))
           })
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ lensr <- evalPlainRoute l
    ; return
        (do{ (lget, lset) <- lensr
           ; return (lget . viewValueWithKey (T.Ref x), lset . overValueWithKey (T.Ref x))
           })
    }

    
splitPlainRoute :: T.PlainRoute -> Cont Scope (Cont Classed (Eval Value -> (Eval Value, Eval Value)))
splitPlainRoute (T.PlainRoute (T.Atom k)) = splitComponent k
  where
    splitComponent :: T.Name T.Rval -> Cont Scope (Cont Classed (Eval Value -> (Eval Value, Eval Value)))
    splitComponent (T.Key r) = 
      do{ kr <- evalRval r
        ; return (do{ k <- bindClassed kr; return (splitWithKey (T.Key k)) })
        }
    splitComponent (T.Ref x) = return (return (splitWithKey (T.Ref x)))

    splitWithKey :: T.Name Value -> Eval Value -> (Eval Value, Eval Value)
    splitWithKey k ev = (viewValueWithKey k ev, unsetValueWithKey k ev)
splitPlainRoute (T.PlainRoute (T.Route l (T.Key r))) =
  do{ kr <- evalRval r
    ; lensr <- evalPlainRoute l
    ; return
        (do{ k <- bindClassed kr
           ; (lget, lset) <- lensr
           ; return (\ ev -> (lget (viewValueWithKey (T.Key k) ev), lset (unsetValueWithKey (T.Key k)) ev))
           })
    }
splitPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ lensr <- evalPlainRoute l
    ; return
        (do{ (lget, lset) <- lensr
           ; return (\ ev -> (lget (viewValueWithKey (T.Ref x) ev), lset (unsetValueWithKey (T.Ref x)) ev))
           })
    }


newtype Bistate s m a = Bistate (State s (Bind m a))
instance Monad m => Monoid (Bistate s m a) where
  mempty = Bistate (return mempty)
  Bistate a `mappend` Bistate b = Bistate (liftA2 mappend a b)

  
bistate :: State s (a -> m a) -> Bistate s m a
bistate = Bistate . fmap Bind

appBistate :: Bistate s m a -> State s (a -> m a)
appBistate (Bistate a) = fmap appBind a 
  
  
evalAssign :: T.Lval -> Cont Classed (Eval Value) -> Scope
evalAssign (T.Laddress l) vr = evalLaddr l (fmap const vr)
evalAssign (T.Lnode xs) vr = m `runCont` id
  where
    unpacks :: Cont Scope (State (Cont Classed (Eval Value)) Scope)
    unpacks = fmap (appBistate . foldMap bistate)
      (mapM evalReversibleStmt xs)
    m =
      do{ unpack <- unpacks
        ; maybe
            (return (fst (runState unpack vr)))
            (\ l -> return (unpackLval l unpack vr))
            (getAlt (foldMap (Alt . collectUnpackStmt) xs))
        }
    
    
    evalReversibleStmt :: T.ReversibleStmt -> Cont Scope (State (Cont Classed (Eval Value)) Scope)
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      -- splitPlainRoute r :: Cont Scope (Cont Classed (Eval Rval -> (Eval Rval, Eval Rval)))
      do{ splitr <- splitPlainRoute keyroute
        ; return 
            (do{ vr <- get
               ; let 
                   m = 
                     do{ vsplit <- splitr
                       ; ev <- vr
                       ; return (vsplit ev)
                       }
               ; put (fst <$> m)
               ; return (evalAssign l (snd <$> m))
               })
        }
    evalReversibleStmt _ = return (return emptyScope)
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> State (Cont Classed (Eval Value)) Scope -> Cont Classed (Eval Value) -> Scope
    unpackLval l unpack vr e = s e >>= evalAssign l wr
      where
        (s, wr) = runState unpack vr
        