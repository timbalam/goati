module Eval
  ( eval
  )
where
import qualified Syntax as T
import qualified Types as U
import qualified Error as E
import Control.Monad.Except
 ( ExceptT
 )
import Control.Monad.Trans.State
 ( StateT
 )

type Except = Either E.Error
type IOExcept = ExceptT E.Error IO

assocLookup :: U.Address -> U.Assoc -> Except U.Value
assocLookup k (U.Assoc x) = maybe (Left E.UnboundVar) Right (lookup k x)

assocExtend :: U.Address -> U.Value -> U.Assoc -> U.Assoc
assocExtend k v (U.Assoc x) = U.Assoc ((k, v):x)

type Eval = StateT { self :: U.Assoc, env :: U.Assoc } Except

selfLookup :: U.Address -> Eval U.Value
selfLookup k = get >>= return . assocLookup k . self

envLookup :: U.Address -> Eval U.Value
envLookup k e = get >>= return .assocLookup k . env

extend :: U.Address -> U.Value -> Eval ()
extend x@(U.Ident _) v = state $ \s e -> ((), (s, assocExtend e x))
extend x@(U.LocalRoute y) v = state $ \s e ->
  let
    newEnv (U.Name y) = assocExtend e (U.Ident y)
    newEnv (U.RelativeRoute (U.Ident x) y) = assocExtend e (U.AbsoluteRoute x y)
    newEnv (U.RelativeRoute (U.Ref _) _) = e    
  in
    ((), (assocExtend s x, newEnv y))
extend x@(U.AbsoluteRoute _ _) v = state $ \s e -> ((), (s, assocExtend e x))

evalRval :: T.Rval -> Eval U.Value
evalRval (T.Number x) = return (U.Number x)
evalRval (T.String x) = return (U.String x)
evalRval (T.Rident x) = envLookup (U.Ident x)
evalRval (T.RabsoluteRoute x y) =
  do{ v <- evalRval x
    ; return $ y `assocLookup` asAssoc v
    }
  where
    asAssoc x@(U.String _) = stringAsAssoc x
    asAssoc x@(U.Number _) = numberAsAssoc x
    asAssoc (U.Node _ x _) = x
evalRval (T.RlocalRoute y) = selfLookup (U.LocalRoute y)
evalRval (T.Rnode _ xs) =
evalRval (T.App x y) =
evalRval (T.Unop s x) =
  evalRval (T.RabsoluteRoute x (asSym s))
evalRval (T.Binop s x y) =
  do{ x' <- T.RabsoluteRoute x (asSym s)
    ; let l = T.Rnode 0 [T.Assign (T.Lident "val") y]
    ; evalRval $ T.RabsoluteRoute (x' `T.App` l) (T.Rident "val")
    }
  

evalStmt :: T.Stmt -> Eval ()
evalStmt (T.Assign k v) =
  do{ x <- toAddress k
    ; y <- evalRval v
    ; extend x y
    }
evalStmt (T.Eval v) = state $ \s e -> 
  do{  evalRval v
evalStmt (T.Unpack v) =
  do{ x <- evalRval v
    ; xs <- asAssoc x
  

toAddress :: T.Lval -> Eval U.Address
toAddress (T.Lident x) = return $ U.Single (toIdent x)
toAddress (T.LlocalRoute y) = toRelativeRoute y >>= return . U.LocalRoute
toAddress (T.LabsoluteRoute x y) = toRelativeRoute y >>= return . U.AbsoluteRoute (toIdent x)
  where
    toIdent (T.Ident x) = U.Ident x
    toName (T.Ref x) = return $ U.Ref x
    toName (T.Key v) = evalRval v >>= return . U.Key
    toRelativeRoute (T.Name x) = toName x >>= return . U.Name
    toRelativeRoute (T.RelativeRoute x y) =
      do{ x' <- toName x
        ; y' <- toRelativeRoute y
        ; return $ U.RelativeRoute x y
        }