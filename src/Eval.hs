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


lookupValue :: T.Name Value -> Getter Value (IOExcept Value)
lookupValue k v =
  do{ liftIO (putStrLn $ "value:")
    ; self <- execNode (unNode v)
    ; liftIO (putStrLn $ ":eulav")
    ; runClasses (lookupSelf k) self
    }


evalName :: T.Name T.Rval -> Eval (Scoped (T.Name IOCValue))
evalName (T.Key r) = (fmap . fmap T.Key) $ evalRval r
evalName (T.Ref x) = return . return $ T.Ref x

sequenceName :: T.Name (IOClasses k) -> IOClasses (T.Name k)
sequenceName (T.Key vr) = T.Key <$> vr
sequenceName (T.Ref x) = return (T.Ref x)

evalRval :: T.Rval -> Eval (Scoped (IOClasses Value))
evalRval (T.Number x) = return . return . return $ Number x
evalRval (T.String x) = return . return . return $ String x
evalRval (T.Rident x) = return $ lookupEnv x
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (Scoped (IOClasses Value))
    evalRoute (T.Route r x) = (liftA2 . liftA2) viewValueWithKey ( (fmap . fmap) sequenceName (evalName x) ) (evalRval r)
    evalRoute (T.Atom x) = (fmap . fmap) ((>>= lookupSelf) . sequenceName) $ evalName x

evalRval (T.Rnode []) = return . return <$> newSymbol
evalRval (T.Rnode stmts) =
  do{ nn <- newNode
    ; npsf <- sequence <$> mapM evalStmt stmts
    ; let npf :: Scoped NodePair
          npf = foldr concatNodePair emptyNodePair <$> npsf
    ; return $
        do{ env <- askScoped
          ; return $
              do{ par <- bindClasses env
                ; let (enode, node) = runScoped npf env'
                      --env' = pure cur
                      env' = concatVtable <$> withNode node <*> pure cur
                      cur = fromDiffList (enode ++ toDiffList par)
                ; return . nn $ node
                }
          }
    }
evalRval (T.App x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; nn <- newNode
    ; let app v w = nn (unNode w ++ unNode v)
    ; return $ (liftA2 . liftClasses2) app vf wf
    }
evalRval (T.Unop sym x) = (fmap . fmap) (>>= liftClasses . evalUnop sym) $ evalRval x
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupValue` x
evalRval (T.Binop sym x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; return $
        do{ mvr <- (liftA2 . liftClasses2) (evalBinop sym) vf wf
          ; return $ mvr >>= liftClasses
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


overNodeWithKey :: T.Name Value -> Setter' Node (IOClasses Value)
overNodeWithKey k f node = return [(k, f)] : node
    
  
unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return [])

 
viewValueWithKey :: IOClasses (T.Name Value) -> Getter (IOClasses Value) (IOClasses Value)
viewValueWithKey kr vr = liftClasses2 lookupValue kr vr >>= liftClasses
      

overValueWithKey :: Monad m => m (IOClasses (T.Name Value)) -> Eval (m (Setter' (IOClasses Value) (IOClasses Value)))
overValueWithKey kf =
  do{ nn <- newNode
    ; return $ 
        do{ kr <- kf
          ; return $ \ f -> fmap nn . liftClasses2 (flip overNodeWithKey f) kr . fmap unNode
          }
    }
    
    
overOrNewValueWithKey :: Monad m => m (IOClasses (T.Name Value)) -> Eval (m (Setter' (IOClasses Value) (IOClasses Value)))
overOrNewValueWithKey kf =
  do{ nn <- newNode
    ; return $ 
        do{ kr <- kf
          ; return $ \ f -> fmap nn . liftClasses2 (flip overNodeWithKey f) kr . unNodeOrEmpty
          }
    }


data LSetter =
    EnvSetter (T.Ident, Setter' IOCValue IOCValue)
  | SelfRefSetter (T.Ident, Setter' IOCValue IOCValue)
  | SelfObjSetter (IOClasses (Value, Setter' IOCValue IOCValue))
  
  
evalLaddr :: T.Laddress -> Eval (Scoped LSetter)
evalLaddr (T.Lident x) = return . return . EnvSetter $ (x, id)
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Eval (Scoped LSetter)
    evalLroute (T.Route l key) =
      do{ kf <- (fmap . fmap) sequenceName (evalName key)
        ; lsetf <- evalLaddr l
        ; vsetf <- overOrNewValueWithKey kf
        ; let compose vset (EnvSetter (x, set)) = EnvSetter (x, set . vset)
              compose vset (SelfRefSetter (x, set)) = SelfRefSetter (x, set . vset)
              compose vset (SelfObjSetter diffr) = SelfObjSetter (over_2 (. vset) <$> diffr)
        ; return $ liftA2 compose vsetf lsetf
        }
    evalLroute (T.Atom k) =
      do{ nf <- evalName k
        ; let setName (T.Key vr) = SelfObjSetter $ liftA2 (,) vr (pure id)
              setName (T.Ref x) = return . SelfRefSetter $ (x, id)
        ; return $ setName <$> nf
        }
    
    
unsetNodeWithKey :: T.Name Value -> Node -> Node
unsetNodeWithKey k node = return [(k, deletes k)] : node

    
unsetValueWithKey :: Monad m => m (IOClasses (T.Name Value)) -> Eval (m (IOClasses Value -> IOClasses Value))
unsetValueWithKey kf =
  do{ nn <- newNode
    ; return $
        do{ kr <- kf
          ; return $ liftClasses2 (\ k -> nn . unsetNodeWithKey k . unNode) kr
          }
    }
    
    
unsetOrEmptyValueWithKey :: Monad m => m (IOClasses (T.Name Value)) -> Eval (m (IOClasses Value -> IOClasses Value))
unsetOrEmptyValueWithKey kf =
  do{ nn <- newNode
    ; return $
        do{ kr <- kf 
          ; return $ liftClasses2 (\ k -> nn . unsetNodeWithKey k) kr . unNodeOrEmpty
          }
    }

    
type NodePair = (EnvNode, Node) 

emptyNodePair = ([], ([], []))

concatNodePair :: NodePair -> NodePair -> NodePair
concatNodePair (enodea, (rsa, krsa)) (enodeb, (rsb, krsb)) = (enodea++enodeb, (rsa++rsb, krsa++krsb))
       
evalStmt :: T.Stmt -> Eval (Scoped NodePair)
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval (Scoped NodePair)
    evalUnassign (T.Lident x) = return . return $ ([(x , deletes x)], ([], []))
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval (Scoped NodePair)
    evalUnassignRoute (T.Route l x) =
      do{ kf <- (fmap . fmap) sequenceName (evalName x)
        ; lsetf <- evalLaddr l
        ; vunsetf <- unsetOrEmptyValueWithKey kf
        ; let apply f (EnvSetter (x, set)) = ([(x, set f)], [])
              apply f (SelfRefSetter (x, set)) = ([], ([(x, set f)], []))
              apply f (SelfObjSetter diffr)    = ([], ([], [pure . over_2 ($ f) <$> diffr]))
        ; return $ liftA2 apply vunsetf lsetf
        }
    evalUnassignRoute (T.Atom x) =
      do{ nf <- evalName x
        ; let assignNodeName (T.Key vr) = ([], [do{ v <- vr; return [(v, deletes v)] })
              assignNodeName (T.Ref x) = ([(x, deletes x), [])
        ; return $ (,) [] . assignNodeName <$> nf
        }
evalStmt (T.Assign l r) = liftA2 (<*>) (evalAssign l) (evalRval r)
evalStmt (T.Unpack r) =
  do{ vf <- evalRval r
    ; return $
        do{ vr <- vf
          ; let selfr =
                  do{ v <- vr
                    ; liftClasses $ execNode (unNode v)
                    }
          ; return $ ([], [toDiffList <$> selfr])
          }
    }
evalStmt (T.Eval r) =
  do{ vf <- evalRval r
    ; return $
        do{ vr <- vf
          ; let selfr =
                  do{ v <- vr
                    ; liftClasses $ execNode (unNode v)
                    }
          ; return ([], [selfr >> return []])
          }
    }
    
    
evalPlainRoute :: T.PlainRoute -> Eval (Scoped (Getter (IOClasses Value) (IOClasses Value), Setter' (IOClasses Value) (IOClasses Value)))
evalPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kf <- evalName key
    ; vsetf <- overValueWithKey kf
    ; return $ liftA2 (,) (viewValueWithKey <$> kf) vsetf
    }
evalPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kf <- evalName key
    ; lensf <- evalPlainRoute l 
    ; vsetf <- overValueWithKey kf
    ; return $
        do{ (lget, lset) <- lensf
          ; kr <- kf
          ; vset <- vsetf
          ; return (lget . viewValueWithKey kr, lset . vset)
          }
    }

    
splitPlainRoute :: T.PlainRoute -> Eval (Scoped (IOClasses Value -> (IOClasses Value, IOClasses Value)))
splitPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kf <- evalName key
    ; vunsetf <- unsetValueWithKey kf
    ; return $
        do{ kr <- kf
          ; vunset <- vunsetf
          ; return $ \ vr ->
              (viewValueWithKey kr vr, vunset vr)
          }
    }
splitPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kf <- evalName key
    ; vunsetf <- unsetValueWithKey kf
    ; lensf <- evalPlainRoute l
    ; return $
        do{ (lget, lset) <- lensf
          ; vunset <- vunsetf
          ; kr <- kf
          ; return $ \ vr ->
              (lget (viewValueWithKey kr vr), lset vunset vr)
          }
    }
    

evalAssign :: T.Lval -> Eval (Scoped (IOClasses Value -> NodePair))
evalAssign (T.Laddress x) = 
  do{ lsetf <- evalLaddr x
    ; let apply f (ESetter (x, set)) = ([(x, set $ f)], [])
          apply f (SSetter diffr) = ([], [pure . over_2 ($ f) <$> diffr])
    ; return . fmap (\ lset -> flip apply lset . const) $ lsetf
    }
evalAssign (T.Lnode xs) =
  do{ unpackfs <- sequence <$> mapM evalReversibleStmt xs
    ; let unpackf = foldr concatUnpack ((,) emptyNodePair) <$> unpackfs
    ; maybe
        (return $ ((view_1 .) <$> unpackf))
        (flip unpackLval unpackf)
        (foldr (<|>) Nothing (map collectUnpackStmt xs))
    }
  where
    concatUnpack :: (IOClasses Value -> (NodePair, IOClasses Value)) -> (IOClasses Value -> (NodePair, IOClasses Value)) -> IOClasses Value -> (NodePair, IOClasses Value)
    concatUnpack unpacka unpackb vr = (np `concatNodePair` np', vr'')
      where
        (np, vr') = unpacka vr
        (np', vr'') = unpackb vr'
    
    evalReversibleStmt :: T.ReversibleStmt -> Eval (Scoped (IOClasses Value -> (NodePair, IOClasses Value)))
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      do{ lassignf <- evalAssign l 
        ; vsplitf <- splitPlainRoute keyroute
        ; let composeOver1 f g = over_1 f . g
        ; return $ liftA2 composeOver1 lassignf vsplitf
        }
    evalReversibleStmt _ = return . return $ (,) emptyNodePair
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> Scoped (IOClasses Value -> (NodePair, IOClasses Value)) -> Eval (Scoped (IOClasses Value -> NodePair))
    unpackLval l unpackf =
      do{ lassignf <- evalAssign l
        ; return $
            do{ unpack <- unpackf
              ; lassign <- lassignf
              ; return $ uncurry concatNodePair . over_2 lassign . unpack
              }
        }
        