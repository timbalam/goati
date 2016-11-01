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

assocLookup :: Assoc T.Rval -> T.Route T.Rval -> Assoc T.Rval -> Except T.Rval
assocLookup e (T.One k) xs = lookupOne e k xs
assocLookup e (T.Many k ks) xs = lookupUpOne e k xs >>= assocLookup e ks . toAssoc
  where
    lookupEither = maybe (Left E.UnboundVar) Right . lookup
    lookupOne k@(T.Ref _) xs = return (lookupEither k xs) >>= evalRval
    lookupOne (T.Key x) xs =
      do{ v <- evalRval x
        ; return (lookupEither (T.Key v) xs) >>= evalRval
        }

assocInsert :: T.Route T.Rval -> T.Rval -> Assoc T.Rval -> Eval (Assoc T.Rval)
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

evalRval :: Assoc T.Rval -> T.Rval -> Except Value
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
  
