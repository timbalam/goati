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
type Rem = IOClasses Value
type Unpack = (Scope, Rem)


view_1 :: Gets' (a, b) a
view_1 = fst


over_1 :: Sets' (a, b) a
over_1 f (a, b) = (f a, b)


view_2 :: Gets' (a, b) b
view_2 = snd

over_2 :: Sets' (a, b) b
over_2 f (a, b) = (a, f b) 


lookupValue :: T.Name Value -> Value -> IOExcept Value
lookupValue k v =
  do{ self <- execEdges (unNode v)
    ; runClasses (lookupVtable k self) self
    }


evalName :: T.Name T.Rval -> Eval Scoped (IOClasses (T.Name Value))
evalName (T.Key r) = T.Key <$> evalRval r
evalName (T.Ref x) = return $ T.Ref x


evalRval :: T.Rval -> Eval Scoped (IOClasses Value)
evalRval (T.Number x) = return $ return (Number x)
evalRval (T.String x) = return $ return (String x)
evalRval (T.Rident x) = return $ lookupEnv (T.Ref x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval Scoped (IOClasses Value)
    evalRoute (T.Route r x) =
      do{ mk <- evalName x
        ; mv <- evalRval r
        ; return $
            do{ k <- mk
              ; v <- mv
              ; liftClasses $ k `lookupValue` v
              }
        }
    evalRoute (T.Atom x) = 
      do{ mk <- evalName x
        ; return $
            do{ k <- mk
              ; lookupSelf k
              }
        }
evalRval (T.Rnode []) = return <$> newSymbol
evalRval (T.Rnode stmts) =
  do{ node <- mapM (mapEval . mapScoped . return evalStmt) stmts
    ; nn <- newNode
    ; env <- askScoped
    ; self <- liftScoped askClasses
    ; let par = bindClasses env
    ; return (nn node')
        where
          node'
          fixEnv env self = 
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


type NSets' = Sets' Node (IOClasses Value)

setNodeWithKey :: T.Name Value -> NSets'
setNodeWithKey k f node = inserts (return k) wr : node
  where
    wr = f . liftClasses $
      do{ self <- execEdges node
        ; runClasses (lookupVtable k self) self
        }
    
    
unsetNodeWithKey :: T.Name Value -> Node -> Node
unsetNodeWithKey k node = deletes (return k) : node
  
  
unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return [])


data LSets' =
    ESets' (IOClasses (Sets' Env (IOClasses Value)))
  | SSets' (IOClasses (Sets' Self (IOClasses Value)))
  

Lcompose :: LSets' -> IOClasses (Sets' (IOClasses Value) (IOClasses)) -> LSets'
Lcompose (ESets' f) g = ESets' (.) <$> f <*> g
Lcompose (SSets' f) g = SSets' (.) <$> f <*> g
  
  
evalLaddr :: T.Laddress -> Eval Scoped LSets'
evalLaddr (T.Lident x) = return . ESets' . return $ \ f er -> overkey k f <$> er
  where
    k = T.Ref x
    overkey k f xs = insertVtable k (f . lookupVtable k $ xs) xs
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Eval Scoped LSets'
    evalLroute (T.Route l key) =
      do{ kr <- evalName key
        ; lsetr <- evalLaddr l
        ; nn <- newNode
        ; let setValueWithKey k f = fmap (nn . setNodeWithKey k f) . unNodeOrEmpty
        ; lsetr `Lcompose` (setValueWithKey <$> kr)
        }
    evalLroute (T.Atom key) =
      do{ kr <- evalName key
        ; return . SSets' $ \ f self ->
            do{ k <- kr
              ; insertVtable k (f . lookupVtable k $ self) self
              }
        }
        
        
type ScopePair = (IOClasses (Env -> Env), IOClasses (Self -> Self))      
       
evalStmt :: T.Stmt -> Eval Scoped ScopePair
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval Scoped ScopePair
    evalUnassign (T.Lident x) = return $ (return envs, return id)
      where
        envs = fmap (deleteVtable (T.Ref x))
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval Scoped ScopePair
    evalUnassignRoute (T.Route l x) =
      do{ kr <- evalName x
        ; lsetr <- setLaddr l
        ; nn <- newNode
        ; let unsetValue k = fmap (nn . unsetNode k) . unNodeOrEmpty
        ; case lsetr of
            ESets' setr -> (setr <*> (unsetValue <$> kr), return id)
            SSets' setr -> (return id, setr <*> (unsetValue <$> kr))
        }
    evalUnassignRoute (T.Atom x) =
      do{ kr <- evalName x
        ; let selfs = deleteVtable <$> kr
        ; return $ (return id, selfs)
        }
evalStmt (T.Assign l r) =
  do{ assignl <- evalAssign l
    ; mapEval . mapScoped (return . flip assignl) $ evalRval r
    }
evalStmt (T.Unpack r) =
  do{ node <- unNode <$> evalRval r
    ; vself <- liftEval . liftScoped . liftClassed $ execEdges node emptyVtable
    ; return $ over_2 (flip concatVtable vself)
    }
evalStmt (T.Eval r) =
  do{ node <- unNode <$> evalRval r
    ; _ <- liftEval . liftScoped . liftClassed $ execEdges node emptyVtable
    ; return id
    }
    
    
viewValueWithKey :: IOClasses (T.Name Value) -> Gets' (IOClasses Value) (IOClasses Value)
viewValueWithKey kr vr =
  do{ k <- kr
    ; v <- vr
    ; liftClasses . lookupValue k v
    }


setValueWithKey :: IOClasses (T.Name Value) -> Eval Scoped (Sets' (IOClasses Value) (IOClasses Value))
setValueWithKey kr =
  do{ nn <- newNode
    ; return $ \ f vr ->
        do{ k <- kr;
          ; v <- vr;
          ; return . nn . setNode k f . unNode $ v
          }
    }

    
evalPlainRoute :: T.PlainRoute -> Eval Scoped (Gets' (IOClasses Value) (IOClasses Value), Sets' (IOClasses Value), (IOClasses Value))
evalPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kr <- evalName key
    ; vset <- setValueWithKey kr
    ; return (viewValue kr, vset)
    }
evalPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kr <- evalName key
    ; (lget, lset) <- evalPlainRoute l 
    ; vset <- setValueWithKey kr
    ; return (lget . viewValue kr, lset . vset)
    }
    
    
unsetValueWithKey :: IOClasses (T.Name Value) -> Eval Scoped (IOClasses Value -> IOClasses Value)
unsetValueWithKey kr =
  do{ nn <- newNode
    ; return $ \ vr ->
        do{ k <- kr
          ; v <- vr
          ; return . nn . (deletes (return k) :) . unNode $ v
          }
    }

    
splitPlainRoute :: T.PlainRoute -> Eval Scoped (IOClasses Value -> (IOClasses Value, IOClasses Value))
splitPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kr <- evalName key
    ; vunset <- unsetValueWithKey kr
    ; return $ \ vr ->
        (viewValue kr vr, vunset vr)
    }
splitPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kr <- evalName key
    ; vunset <- unsetValueWithKey kr
    ; (lget, lset) <- evalPlainRoute l
    ; return $ \ vr ->
        (lget . viewValue kr vr, lset . vunset vr)
    }
    

evalAssign :: T.Lval -> Eval Scoped (IOClasses Value -> [ScopePair])
evalAssign (T.Laddress x) = 
  do{ lset <- setLaddr x
    ; return $ \ vr -> case lset of
        ESets' setr -> [(envs, return id)]
          where
            envs = do{ set <- setr; return $ flip set (const vr) }
        SSets' setr -> [(return id, selfs)]
          where
            selfs = do{ set <- setr; return $ flip set (const vr) }
    }
evalAssign (T.Lnode xs) = 
  do{ b <- curry . foldr (.) id . map uncurry <$> mapM evalReversibleStmt xs
    ; maybe
        (return $ \ s vr -> view_1 $ b s vr)
        (\l -> unpackLval l b)
        (foldr (<|>) Nothing (map collectUnpackStmt xs))
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval Scoped (IOClasses Value -> ([ScopePair], IOClasses Value))
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      do{ lassign <- evalAssign l 
        ; vsplit <- splitPlainRoute keyroute
        ; return $ over_1 lassign . vsplit
        }
    evalReversibleStmt _ = return $ \ v -> ([(return id, return id)], v)
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> (IOClasses Value -> ([ScopePair], IOClasses Value)) -> Eval Scoped (IOClasses Value -> [ScopePair])
    unpackLval l unpack =
      do{ lassign <- evalAssign l
        ; return $ \ vr -> ss++ss'
            where
              (ss, vr') = unpack vr
              ss' = lassign vr'
        }
        