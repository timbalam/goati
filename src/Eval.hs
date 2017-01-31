module Eval
  ( evalRval
  )
where
import Control.Monad.Except
  ( throwError
  , catchError
  )
import Control.Monad.Trans.State
  ( StateT
  , evalStateT
  , execStateT
  , State
  , evalState
  , execState
  , get
  , put
  )
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
import Control.Applicative( (<|>) )
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Gets' s a = s -> a
type Sets' s a = (a -> a) -> s -> s
type Scope = (Env, Node)
type Rem = IOClassed Value
type Unpack = (Scope, Rem)


view_1 :: Gets' (a, b) a
view_1 = fst


over_1 :: Sets' (a, b) a
over_1 f (a, b) = (f a, b)


view_2 :: Gets' (a, b) b
view_2 = snd

over_2 :: Sets' (a, b) b
over_2 f (a, b) = (a, f b) 

  
viewValue :: T.Name Value -> Gets' (IOClasses Value) (IOClasses Value)
viewValue k vr =
  do{ v <- vr
    ; liftClasses $
        do{ es <- unNode v []
          ; self <- execEdges es
          ; runClasses (lookupVtable k self) self
          }
    }


overValue :: T.Name Value -> Sets' (Classes (Eval IOExcept) Value) (Classes (Eval IOExcept) Value)
overValue k f vr =
  do{ nn <- liftClasses newNode
    ; v <- vr
    ; return . nn $ \ super = 
        do{ es <- unNode v super
          ; self <- execEdges es
          ; let wr = f . liftClasses . liftEval . runClasses (lookupVtable k self) $ self
          ; return $ insertEdge (return k) wr es
          }
    }


unsetValue :: T.Name Value -> Staged (Eval IOClassed) Value -> Staged (Eval IOClassed) Value
unsetValue k vr =
  do{ nn <- liftStaged newNode
    ; v <- vr
    ; return . nn $ (deleteEdge (return k) <$>) . unNode v
    }
    
overStaged :: Sets' (Staged a) (IOClassed a)
overStaged f s = s >>= liftStaged . f . return


evalName :: T.Name T.Rval -> Eval IOScopes (T.Name Value)
evalName (T.Key r) = T.Key <$> evalRval r
evalName (T.Ref x) = return $ T.Ref x


evalRval :: T.Rval -> Eval (Scoped IOClasses) Value
evalRval (T.Number x) = return $ Number x
evalRval (T.String x) = return $ String x
evalRval (T.Rident x) = liftEval . liftScoped $ lookupEnv (T.Ref x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (Scoped IOClasses) Value
    evalRoute (T.Route r x) =
      do{ k <- evalName x
        ; v <- evalRval r
        ; liftEval . liftScoped $ viewValue k (return v)
        }
    evalRoute (T.Atom x) = 
      do{ k <- evalName x
        ; liftEval . liftScoped $ lookupSelf k
        }
evalRval (T.Rnode []) = newSymbol
evalRval (T.Rnode stmts) =
  do{ b <- foldr (.) id <$> mapM evalStmt stmts
    ; nn <- newNode
    ; return $
        do{ env <- askScoped
          ; self <- liftScoped askClassed
          ; let par = local (const self) $ bindClassed env
                node super = mself'
                  where
                    scope = (par, super) 
                    mscope = runScoped (b $ return scope) menv'
                    mself' = view_2 <$> mscope
                    menv' = 
                      do{ (env, self') <- liftClassed mscope
                        ; concatVtable <$> withSelf self' <*> env
                        }
          ; return . nn $ node
          }
    }
evalRval (T.App x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; nn <- newNode
    ; return $ 
        do{ v <- vf
          ; w <- wf
          ; return . nn $ (unNode w =<<) . unNode v
          }
    }
evalRval (T.Unop sym x) =
  do{ vf <- evalRval x
    ; return $
        do{ v <- vf
          ; liftScoped $ evalUnop sym v
          }
    }
  where
    evalUnop :: T.Unop -> Value -> IOClassed Value
    evalUnop sym (Number x) = liftClassed $ primitiveNumberUnop sym x
    evalUnop sym (Bool x) = liftClassed $ primitiveBoolUnop sym x
    evalUnop sym x = liftClassed (unNode x emptyVtable) >>= lookupVtable (T.Key (unopSymbol sym))
evalRval (T.Binop sym x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; return $
        do{ v <- vf
          ; w <- wf
          ; liftScoped $ evalBinop sym v w
          }
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOClassed Value
    evalBinop sym (Number x) (Number y) = liftClassed $ primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = liftClassed $ primitiveBoolBinop sym x y
    evalBinop sym x y = 
      do{ xs <- liftClassed $ unNode x emptyVtable
        ; xop <- T.Key (binopSymbol sym) `lookupVtable` xs
        ; ys <- liftClassed $ unNode xop emptyVtable
        ; let ys' = insertVtable (T.Key rhsSymbol) (return y) ys
        ; T.Key resultSymbol `lookupVtable` ys'
        }
evalRval (T.Import x) = evalRval x


evalLaddr :: T.Laddress -> Eval (Scoped IOClasses) Value
evalLaddr (T.Lident x) = liftEval . liftScoped $ lookupEnv (T.Ref x)
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Eval (Scoped IOClasses) Value
    evalLroute (T.Route l key) =
      do{ k <- evalName key
        ; v <- evalLaddr l
        ; liftEval . liftScoped $ viewValue k (return v)
        }
    evalLroute (T.Atom key) =
      do{ k <- evalName key
        ; liftEval . liftScoped $ lookupSelf k
        }

       
       
evalStmt :: T.Stmt -> Eval (Scoped Identity) (Scope -> Scope)
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval (Scoped Identity) (Scope -> Scope)
    evalUnassign (T.Lident x) = return . over_1 . fmap $ deleteVtable (T.Ref x)
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval (Scoped Identity) (Scope -> Scope)
    evalUnassignRoute (T.Route l x) =
      do{ nn <- newNode
        ; vf <- evalLaddr l
        ; kf <- evalName x
        ; evalAssign (T.Laddress l) <*> pure $
            do{ vs <- vf
              ; ks <- kf
              ; return $
                  do{ node' <- catchUnboundVar (unNode <$> vs) (return return)
                    ; return . nn $ \ super -> deleteEdge ks <$> node' super
                    }
              }
        }
    evalUnassignRoute (T.Atom x) =
      do{ ks <- mapEval . mapScoped return $ foldFree (mapEval . mapScoped liftStaged) (evalName x)
        ; return $ over_2 (\ node super -> deleteEdge ks <$> node super)
        }
evalStmt (T.Assign l r) = evalAssign l <*> evalRval r
evalStmt (T.Unpack r) =
  do{ vf <- evalRval r
    ; return $ \ sf ->
        do{ vs <- mapScoped (return . runIdentity) vf
          ; let x =
              do{ v <- vs
                ; liftClassed $ unNode v [] >>= execEdges
                }
          ; (fmap . over_2) (\ node super ->  x : node super) sf
          }
    }
evalStmt (T.Eval r) =
  do{ vf <- evalRval r
    ; return $ \ sf ->
        do{ vs <- mapScoped (return . runIdentity) vf
          ; let x =
              do{ v <- vs
                ; _ <- liftClassed $ unNode v [] >>= execEdges
                ; return $ emptyVtable
                }
          ; (fmap . over_2) (\ node super -> x : node super) sf
          }
    }


evalAssign :: T.Lval -> Eval (Scoped IOClasses) Value -> Eval (Scoped Identity) (Scope -> Scope)
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval (Scoped IOClasses) Value -> Eval (Scoped Identity) (Scope -> Scope)
    evalAssignLaddress (T.Lident x) =
      return $ \ vf sf ->
        do{ let k = T.Ref x
          ; vs <- mapScoped (return . runIdentity) vf
          ; (fmap . over_1 . fmap) (insertVtable k (retract vs)) sf
          }
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval (Scoped IOClasses) Value -> Eval (Scoped Identity) (Scope -> Scope)
    evalAssignRoute (T.Route l key) =
      do{ nn <- newNode
        ; vr <- mapEval . mapScoped return $ evalLaddr l
        ; kr <- mapEval . mapScoped return $ evalName key
        ; assignLhs <- evalAssignLaddress l
        ; return $ \ wr en@(_, node') -> assignLhs (return node) en
            where
              node super =
                do{ self <- node' super >>= execEdges
                  ; node'' <- catchUnboundVar (runClasses vr self >>= unNode) (return return)
                  ; insertEdge kr wr <$> node'' super
                  }
        }
    evalAssignRoute (T.Atom key) =
      do{ kf <- evalName key
        ; return $ \ vf sf ->
            do{ vs <- mapScoped (return . runIdentity) vf
              ; ks <- mapScoped (return . runIdentity) kf
              ; (fmap . over_2) (insertEdge ks vs) sf
              }
        }
evalAssign (T.Lnode xs) = 
  do{ b <- foldr (.) id <$> mapM evalReversibleStmt xs
    ; maybe
        (return $ \ vf sf -> view_1 <$> b ((,) <$> sf <*> mapScoped pure vf))
        (\l -> unpackLval l b)
        (foldr (<|>) Nothing (map collectUnpackStmt xs))
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval (IOScoped Unpack -> IOScoped Unpack)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ assignRem <- (.) <$> evalAssign l <*> viewPlainRoute keyroute
        ; unsetRem <- unsetPlainRoute keyroute
        ; return $ \ sf ->
            do{ (scope, rem) <- sf
              ; scope' <- assignRem (liftScoped rem) (return scope)
              ; rem'  <- mapScoped return . unsetRem $ liftScoped rem
              ; return (scope', rem')
              }
        }
    evalReversibleStmt _ = return id
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> (Scoped' Unpack -> Scoped' Unpack) -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope)
    unpackLval l b = 
      do{ assignLhs <- evalAssign l
        ; return $ \ vf sf ->
          do{ (scope', rem') <- b ((,) <$> sf <*> mapScoped pure vf)
            ; assignLhs (liftScoped rem') (return scope')
            }
        }
        
    viewEdge :: Scoped (Staged (T.Name Value)) -> Gets' (Scoped (Staged Value)) (Scoped (Staged Value))
    viewEdge kf vf =
      do{ f <- (fmap . fmap) viewValue kf
        ; fmap (>>= liftStaged . f . return) vf
        }
        
    viewPlainRoute :: T.PlainRoute -> Eval (Gets' (Scoped (Staged Value)) (Scoped (Staged Value)))
    viewPlainRoute (T.PlainRoute (T.Atom key)) = 
      viewEdge <$> evalName key
    viewPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (viewEdge <$> evalName key) <*> viewPlainRoute l
        
    overPlainRoute :: T.PlainRoute -> Eval (Sets' (Scoped (Staged Value)) (Scoped (Staged Value)))
    overPlainRoute (T.PlainRoute (T.Atom key)) =
      do{ kf <- evalName key
        ; over <- (fmap . fmap) overValue kf
        ; liftOver <$> overValue k
        }
    overPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (evalName key >>= overValue >>= return . liftOver) <*> overPlainRoute l
    
    
    --Scoped (Staged (Eval (Scoped (Staged a)))) -> Eval (Scoped (Staged a))
    sequenceStaged :: Staged (Eval a) -> Eval (Staged a)
    sequenceStaged (Pure m) = Pure <$> m
    sequenceStaged (Free f) = State $ s ->
      do{ m <- f
        ; let (a, s) = runState (sequenceStaged m) s
    
    sequenceScoped :: Scoped (Eval a) -> Eval (Scoped a)
      
    liftOver :: (Monad m, Monad n) => Sets' (m a) (n b) -> Sets' (Scoped m a) (Scoped n b)
    liftOver over f vf =
      do{ env <- askScoped
        ; let f' wr = runScoped (f $ liftScoped wr) env
        ; mapScoped (over f') vf
        }
    
    
    unsetPlainRoute :: T.PlainRoute -> Eval (Scoped IOClassed Value -> Scoped IOClassed Value)
    unsetPlainRoute (T.PlainRoute (T.Atom key)) = evalName key >>= unsetValue >>= return . mapScoped
    unsetPlainRoute (T.PlainRoute (T.Route l key)) = overPlainRoute l <*> (evalName key >>= unsetValue >>= return . mapScoped)
        