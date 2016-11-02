module Eval
  ( eval
  )
where
import qualified Syntax as T
import Types
 ( Assoc
 , Value(..)
 )
import qualified Error as E
import Control.Monad.Except
 ( ExceptT
 )
import Control.Monad.Trans.State
 ( StateT
 )

type Except = Either E.Error
type IOExcept = ExceptT E.Error IO
type Eval = StateT Assoc Except

assocLookup :: T.Route Value -> Assoc -> Except Value
assocLookup (T.One k) = lookupOne k 
assocLookup (T.Many k ks) xs = lookupOne k xs >>= assocLookup ks . toAssoc
  where
    lookupOne k = maybe (Left E.UnboundVar) Right . lookup k

mapMRoute :: (a -> m b) -> T.Route a -> m (T.Route b)
mapMRoute f (T.One x) = f x >>= T.One
mapMRoute f (T.Many x xs) =
  do{ v <- f x
    ; vs <- mapRoute f xs
    ; return (T.Many v vs)
    }
    
evalRval :: T.Rval -> Eval Value
evalRval (T.Number x) = return (Number x)
evalRval (T.String x) = return (String x)
evalRval (T.Rident x) = getEnv >>= return . assocLookup (T.One (T.Ref x))
evalRval (T.RabsoluteRoute x xs) =
  do{ v <- evalRval x
    ; vs <- mapMRoute evalRval xs
    ; return (assocLookup vs (toAssoc v))
    }
evalRval (T.RlocalRoute (T.Many x xs)) = getSelf >>= return . assocLookup xs



assocInsert :: T.Route Value -> Value -> Assoc -> Eval
assocInsert (T.One k) v xs = return ((k,v):xs)
assocInsert (T.Many k ks) v xs = assocLookup (T.One k) xs >>= assocInsert ks v . toAssoc
  
assocConcat :: Assoc a -> Assoc a -> Assoc a
assocConcat = (++)



evalLookup :: T.Lval -> Eval Value
evalLookup (T.Lident k) = envLookup (T.One (T.Ref k))
evalLookup (T.LabsoluteRoute k ks) = envLookup (T.Many (T.Ref k) ks)
evalLookup (T.LlocalRoute ks) = selfLookup ks
  where
    selfLookup k = get >>= assocLookup k . self
    envLookup k = get >>= assocLookup k . env

evalInsert :: T.Lval -> T.Rval -> Eval ()
evalInsert (T.Lident k) v = envInsert (T.One (T.Ref k)) v
evalInsert (T.LabsoluteRoute k ks) v = envInsert (T.Many (T.Ref k) ks) v
evalInsert (T.LlocalRoute ks) v = selfInsert ks v >> envInsert ks v
  where
    selfInsert k v = modify $ \i s e -> (i, assocInsert k v s, e)
    envInsert k v = modify $ \i s e -> (i, s, assocInsert k v e)
    
evalConcat :: T.Rval -> Eval ()
evalConcat x = 
  do{ x' <- evalRval x
    ; let a = toAssoc x'
    ; modify $ \i s e -> (i, assocConcat a s, assocConcat a e)
    }

evalRval _ (T.Number x) = return (Number x)
evalRval _ (T.String x) = return (String x)
evalRval e (T.Rident x) = assocLookup (T.One (T.Ref x)) e
evalRval e (T.RabsoluteRoute x xs) = evalRval e x >>= assocLookup e xs . toAssoc
evalRval e (T.RlocalRoute xs) = selfLookup e xs
evalRval (T.Rnode xs) = evalNew >> evalStmts xs >> evalGetNode
evalRval (T.App x y) = 
  do{ x' <- evalRval x
    ; y' <- evalRval y
    ; let ax = toAssoc x'
    ; let ay = toAssoc y'
    ; node (ax `assocConcat` ay)
    }
evalRval (T.Unop s x) =
  evalRval (T.RabsoluteRoute x (asSym s))
evalRval (T.Binop s x y) =
  do{ x' <- T.RabsoluteRoute x (asSym s)
    ; l <- node [T.Assign (T.Lident "val") y]
    ; evalRval $ T.RabsoluteRoute (x' `T.App` l) (T.Rident "val")
    }
  

evalStmts :: [T.Stmt] -> Eval ()
evalStmts xs = 
  do{ (us, vs) <- foldM sortStmt ([], []) xs 
    ; mapM_ unpack us
    ; mapM_ evalRval vs
    }
  where
    sortStmt (us, vs) (T.Assign k v) = evalInsert k v >> return (us, vs)
    sortStmt (us, vs) (T.Eval v) = return (us, v:vs)
    sortStmt (us, vs) (T.Unpack u) = return (u:us, vs)
    unpack u = evalConcat u
  
