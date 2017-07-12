{-# LANGUAGE FlexibleContexts #-}
module Types.Eval.Value
  ( Env
  , Self
  , Node
  , Cell
  , IX
  , IXW
  , emptyEnv
  , emptyNode
  , newNode
  , unNode
  , Value(..)
  , primitiveNumberBinop
  , primitiveNumberSelf
  , primitiveBoolBinop
  , primitiveBoolSelf
  , primitiveStringSelf
  , primitiveBindings
  )
  where
import Control.Monad.Catch( throwM, MonadThrow )
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Exception
import qualified Data.Map as M
import Data.IORef
import Data.Typeable

import qualified Types.Parser as T
import qualified Types.Error as E
import Types.Eval.Ided
import Types.Eval.Cell
import Types.Eval.Scope
import Types.Util

-- Env / Self
type IX = Ided IO
type Cell = IORef (IX Value)
type Env = M.Map T.Ident Cell
type Self = Env
type IXW = EWriterT IX () IX
type Node = Classed IXW Self

emptyEnv :: Env
emptyEnv = M.empty

emptyNode :: Node
emptyNode = mempty

-- Value
data NodeId = NodeId Id | Input
  deriving (Eq, Ord)
instance Show NodeId where show = showNodeId
        
showNodeId :: NodeId -> String
showNodeId (NodeId i) = show i
showNodeId Input = "Input"

data Value = String String | Number Double | Bool Bool | Node NodeId (IORef (Maybe Self)) Node
instance Show Value where
  show (String x) = show x
  show (Number x) = show x
  show (Bool x)   = show x
  show (Node i _ _) = "<Node:" ++ show i ++ ">"
instance Eq Value where
  String x == String x' = x == x'
  Number x == Number x' = x == x'
  Bool x == Bool x' = x == x'
  Node x _ _ == Node x' _ _ = x == x'
  _ == _ = False
instance Ord Value where
  compare (String x)          (String x')          = compare x x'
  compare (String _)          _                    = LT
  compare _                   (String _)           = GT
  compare (Number x)          (Number x')          = compare x x'
  compare (Number _)          _                    = LT
  compare _                   (Number _)           = GT
  compare (Bool x)            (Bool x')            = compare x x'
  compare (Bool _)            _                    = LT
  compare _                   (Bool _)             = GT
  compare (Node x _ _)        (Node x' _ _)        = compare x x'
  
newNode :: (MonadState Ids m, MonadIO m) => m (Node -> Value)
newNode = useId (Node . NodeId) <*> liftIO (newIORef Nothing)
    
unNode :: Value -> Node
unNode = go
  where
    go (Number x) = selfToNode (primitiveNumberSelf x)
    go (String x) = selfToNode (primitiveStringSelf x)
    go (Bool x) = selfToNode (primitiveBoolSelf x)
    go (Node _ _ c) = c
    
    selfToNode :: IX Self -> Node
    selfToNode m = EndoM (\ self0 -> M.union <$> (lift . lift) m <*> pure self0)

    
-- Primitives
primitiveStringSelf :: MonadIO m => String -> m Self
primitiveStringSelf x = return emptyEnv

primitiveNumberSelf :: MonadIO m => Double -> m Self
primitiveNumberSelf x = return emptyEnv

primitiveBoolSelf :: MonadIO m => Bool -> m Self
primitiveBoolSelf x = return emptyEnv

primitiveNumberUnop :: MonadThrow m => T.Unop -> Double -> m Value
primitiveNumberUnop (T.Neg) x = return . Number $ negate x
primitiveNumberUnop s       _ = E.throwUndefinedNumberOp s

primitiveBoolUnop :: MonadThrow m => T.Unop -> Bool -> m Value
primitiveBoolUnop (T.Not) x = return . Bool $ not x
primitiveBoolUnop s       _ = E.throwUndefinedBoolOp s

primitiveNumberBinop :: MonadThrow m => T.Binop -> Double -> Double -> m Value
primitiveNumberBinop (T.Add)  x y = return . Number $ x + y
primitiveNumberBinop (T.Sub)  x y = return . Number $ x - y
primitiveNumberBinop (T.Prod) x y = return . Number $ x * y
primitiveNumberBinop (T.Div)  x y = return . Number $ x / y
primitiveNumberBinop (T.Pow)  x y = return . Number $ x ** y
primitiveNumberBinop (T.Lt)   x y = return . Bool $ x < y
primitiveNumberBinop (T.Gt)   x y = return . Bool $ x > y
primitiveNumberBinop (T.Eq)   x y = return . Bool $ x == y
primitiveNumberBinop (T.Ne)   x y = return . Bool $ x /= y
primitiveNumberBinop (T.Le)   x y = return . Bool $ x <= y
primitiveNumberBinop (T.Ge)   x y = return . Bool $ x >= y
primitiveNumberBinop s        _ _ = E.throwUndefinedNumberOp s

primitiveBoolBinop :: MonadThrow m => T.Binop -> Bool -> Bool -> m Value
primitiveBoolBinop (T.And) x y = return . Bool $ x && y
primitiveBoolBinop (T.Or)  x y = return . Bool $ x || y
primitiveBoolBinop (T.Lt)  x y = return . Bool $ x < y
primitiveBoolBinop (T.Gt)  x y = return . Bool $ x > y
primitiveBoolBinop (T.Eq)  x y = return . Bool $ x == y
primitiveBoolBinop (T.Ne)  x y = return . Bool $ x /= y
primitiveBoolBinop (T.Le)  x y = return . Bool $ x <= y
primitiveBoolBinop (T.Ge)  x y = return . Bool $ x >= y
primitiveBoolBinop s       _ _ = E.throwUndefinedBoolOp s

inputNode :: MonadIO m => m Value
inputNode =
  Node
    Input
    <$> liftIO (newIORef Nothing)
    <*> pure
      (EndoM (\ self ->
         M.insert (T.Ident "getLine") <$> newCell (liftIO getLine >>= return . String) <*> pure self))

primitiveBindings :: MonadIO m => m Env
primitiveBindings = 
  M.insert (T.Ident "input")
    <$> newCell inputNode
    <*> pure emptyEnv


    
