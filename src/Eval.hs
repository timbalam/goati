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

type Getter s a = s -> a
type Setter s a = (a -> a) -> s -> s


view_1 :: Getter (a, b) a
view_1 = fst


over_1 :: Setter (a, b) a
over_1 f (a, b) = (f a, b)


view_2 :: Getter (a, b) b
view_2 = snd


over_2 :: Setter (a, b) b
over_2 f (a, b) = (a, f b)



lookupValue :: T.Name Value -> Getter Value (IOExcept Value)
lookupValue k v =
  do{ self <- execNode (unNode v)
    ; runClasses (lookupSelf k) self
    }


evalName :: T.Name T.Rval -> Eval Scoped (IOClasses (T.Name Value))
evalName (T.Key r) = fmap . fmap T.Key $ evalRval r
evalName (T.Ref x) = return . return $ T.Ref x


sequenceName :: Applicative m => T.Name (m a) -> m (T.Name a)
sequenceName (T.Key m) = T.Key <$> m
sequenceName (T.Ref x) = pure (T.Ref x)


evalRval :: T.Rval -> Eval Scoped (IOClasses Value)
evalRval (T.Number x) = return $ return (Number x)
evalRval (T.String x) = return $ return (String x)
evalRval (T.Rident x) = return $ lookupEnv x
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval Scoped (IOClasses Value)
    evalRoute (T.Route r x) = viewValueWithKey <$> evalName x <*> evalRval r
    evalRoute (T.Atom x) = 
      do{ kr <- evalName x
        ; return $ 
            do{ k <- kr
              ; lookupSelf k
              }
        }
evalRval (T.Rnode []) = return <$> newSymbol
evalRval (T.Rnode stmts) =
  do{ nn <- newNode
    ; npr <- mapEval return $ foldr concatNodePair emptyNodePair <$> mapM evalStmt stmts
    ; env <- liftEval askScoped
    ; return $
        do{ par <- bindClasses env
          ; let (enode, node) = runScoped npr env'
                env' = concatVtable <$> withNode node <*> pure cur
                cur = M.mapWithKey (\k f -> f (throwUnboundVar k)) $ unionWith (.) (M.fromListWith (flip (.)) enode) (map const par)
          ; return . nn $ node
          }
    }
evalRval (T.App x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; nn <- newNode
    ; let app v w = nn (unNode w : unNode v)
    ; return $ (app <$> vr) `zipClasses` wr 
    }
evalRval (T.Unop sym x) =
  do{ vr <- evalRval x
    ; return $
        do{ v <- vr
          ; liftClasses $ evalUnop sym v
          }
    }
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupValue` x
evalRval (T.Binop sym x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; mv <- (evalBinop sym <$> vr) `zipClasses` wr
    ; liftClasses mv
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y =
      do{ opnode <- unNode <$> T.Key (binopSymbol sym) `lookupValue` x
        ; let opnode' = overNodeWithKey (T.Key rhsSymbol) (const $ return y) opnode
        ; self <- execEdges opNode
        ; runClasses (lookupSelf (T.Key resultSymbol)) self
        }
evalRval (T.Import x) = evalRval x


overNodeWithKey :: T.Name Value -> Setter Node (IOClasses Value)
overNodeWithKey k f node = return (k, f) : node
    
  
unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return emptyNode)

 
viewValueWithKey :: T.Name (IOClasses Value) -> Getter (IOClasses Value) (IOClasses Value)
viewValueWithKey kr vr = ((lookupValue <$> kr) `zipClasses` vr) >>= liftClasses
      

overValueWithKey :: IOClasses (T.Name Value) -> Eval Scoped (Setter (IOClasses Value) (IOClasses Value))
overValueWithKey kr =
  do{ nn <- newNode
    ; return $ \ f -> zipClasses (nn . flip overNodeWithKey f <$> kr) . fmap unNode
    }
    
    
overOrNewValueWithKey :: IOClasses (T.Name Value) -> Eval Scoped (Setter (IOClasses Value) (IOClasses Value))
overOrNewValueWithKey kr =
  do{ nn <- newNode
    ; return $ \ f -> zipClasses (nn . flip overNodeWithKey f <$> kr) . unNodeOrEmpty
    }


data LSetter =
    ESetter (T.Ident, Setter (IOClasses Value) (IOClasses Value))
  | SSetter (IOClasses (T.Name Value, Setter (IOClasses Value) (IOClasses Value)))
  
  
evalLaddr :: T.Laddress -> Eval Scoped LSetter
evalLaddr (T.Lident x) = return $ ESetter (x, id)
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Eval Scoped LSetter
    evalLroute (T.Route l key) =
      do{ kr <- evalName key
        ; lsetr <- evalLaddr l
        ; vset <- overOrNewValueWithKey kr
        ; case lsetr of
            ESetter (x, set) -> ESetter (x, set . vset)
            SSetter diffr -> SSetter (over_2 (. vset) <$> diffr)
        }
    evalLroute (T.Atom k) =
      do{ kr <- evalName k
        ; return $ SSetter ((,) <$> kr <*> pure id)
        }
    
    
unsetNodeWithKey :: T.Name Value -> Node -> Node
unsetNodeWithKey k node = return (k, deletes k) : node

    
unsetValueWithKey :: IOClasses (T.Name Value) -> Eval Scoped (IOClasses Value -> IOClasses Value)
unsetValueWithKey kr =
  do{ nn <- newNode
    ; return $ zipClasses (nn . unsetNodeWithKey <$> kr) . fmap unNode
    }
    
    
unsetOrNewValueWithKey :: IOClasses (T.Name Value) -> Eval Scoped (IOClasses Value -> IOClasses Value)
unsetOrNewValueWithKey kr =
  do{ nn <- newNode
    ; return $ zipClasses (nn . unsetNodeWithKey <$> kr) . unNodeOrEmpty
    }
        
        
type NodePair = (EnvNode, Node) 

emptyNodePair = ([], [])

concatNodePair :: NodePair -> NodePair -> NodePair
concatNodePair (esa, ssb) (esb, ssb) = (esa++esb, ssa++ssb)
       
evalStmt :: T.Stmt -> Eval Scoped NodePair
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval Scoped NodePair
    evalUnassign (T.Lident x) = return $ ([(x , deletes x)], [])
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval Scoped NodePair
    evalUnassignRoute (T.Route l x) =
      do{ kr <- evalName x
        ; lsetr <- evalLaddr l
        ; vunset <- unsetOrEmptyValueWithKey kr
        ; return $ case lsetr of
            ESetter (x, set) -> ([(x, set . vunset)], [])
            SSetter diffr -> ([], [over_2 (. vunset) <$> diffr])
        }
    evalUnassignRoute (T.Atom x) =
      do{ kr <- evalName x
        ; return $ ([], [do{ v <- vr; return [(v, deletes v)] }])
        }
evalStmt (T.Assign l r) = evalAssign l <*> evalRval r
evalStmt (T.Unpack r) =
  do{ vr <- evalRval r
    ; let selfr =
            do{ v <- vr
              ; liftClassed $ execNode (unNode v)
              }
    ; return $ ([], [toList . map const <$> selfr])
    }
evalStmt (T.Eval r) =
  do{ vr <- evalRval r
    ; let selfr =
            do{ v <- vr
              ; liftClassed $ execEdges (unNode v) emptyVtable
              }
    ; return ([], [selfr >> return []])
    }
    
    
evalPlainRoute :: T.PlainRoute -> Eval Scoped (Getter (IOClasses Value) (IOClasses Value), Setter (IOClasses Value), (IOClasses Value))
evalPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kr <- evalName key
    ; vset <- overValueWithKey kr
    ; return (viewValueWithKey kr, vset)
    }
evalPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kr <- evalName key
    ; (lget, lset) <- evalPlainRoute l 
    ; vset <- overValueWithKey kr
    ; return (lget . viewValueWithKey kr, lset . vset)
    }

    
splitPlainRoute :: T.PlainRoute -> Eval Scoped (IOClasses Value -> (IOClasses Value, IOClasses Value))
splitPlainRoute (T.PlainRoute (T.Atom key)) =
  do{ kr <- evalName key
    ; vunset <- unsetValueWithKey kr
    ; return $ \ vr ->
        (viewValueWithKey kr vr, vunset vr)
    }
splitPlainRoute (T.PlainRoute (T.Route l key)) =
  do{ kr <- evalName key
    ; vunset <- unsetValueWithKey kr
    ; (lget, lset) <- evalPlainRoute l
    ; return $ \ vr ->
        (lget . viewValueWithKey kr vr, lset . vunset vr)
    }
    

evalAssign :: T.Lval -> Eval Scoped (IOClasses Value -> NodePair)
evalAssign (T.Laddress x) = 
  do{ lset <- evalLaddr x
    ; return $ \ vr -> case lset of
        ESetter (x, set) -> ([(x, set $ const vr)], [])
        SSetter diffr -> ([], [(:[]) . over_2 ($ const vr) <$> diffr])
    }
evalAssign (T.Lnode xs) =
  do{ unpack <- foldr concatUnpack ((,) emptyNodePair) <$> mapM evalReversibleStmt xs
    ; maybe
        (return $ view_1 . unpack)
        (flip unpackLval unpack)
        (foldr (<|>) Nothing (map collectUnpackStmt xs))
    }
  where
    concatUnpack :: (IOClasses Value -> (NodePair, IOClasses Value)) -> (IOClasses Value -> (NodePair, IOClasses)) -> IOClasses Value -> (NodePair, IOClasses Value)
    concatUnpack unpacka unpackb vr = (np `concatNodePair` np', vr'')
      where
        (np, vr') = unpacka vr
        (np', vr'') = unpackb vr'
    
    evalReversibleStmt :: T.ReversibleStmt -> Eval Scoped (IOClasses Value -> (NodePair, IOClasses Value))
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      do{ lassign <- evalAssign l 
        ; vsplit <- splitPlainRoute keyroute
        ; return $ over_1 lassign . vsplit
        }
    evalReversibleStmt _ = return $ (,) emptyNodePair
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> (IOClasses Value -> (NodePair, IOClasses Value)) -> Eval Scoped (IOClasses Value -> NodePair)
    unpackLval l unpack =
      do{ lassign <- evalAssign l
        ; return $ \ vr -> np `concatNodePair` np'
            where
              (np, vr') = unpack vr
              np' = lassign vr'
        }
        