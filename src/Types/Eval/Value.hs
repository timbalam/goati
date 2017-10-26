{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Types.Eval.Value
  ( Env
  , Self
  , Node
  , Cell
  , IOW
  , emptyEnv
  , emptyNode
  , newNode
  , unNode
  , Value(..)
  , primitiveNumberUnop
  , primitiveNumberBinop
  , primitiveNumberSelf
  , primitiveBoolUnop
  , primitiveBoolBinop
  , primitiveBoolSelf
  , primitiveStringSelf
  , primitiveBindings
  )
  where
  

import Types.Parser( Binop(..), Unop(..), ShowMy(..) )
import qualified Types.Error as E
import Types.Eval.Ided
import Types.Eval.Cell
import Types.Util.Configurable

import qualified Data.Text as T
import Control.Monad.Catch( throwM, MonadThrow )
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Exception
import qualified Data.Map as M
import Data.Typeable


-- Env / Self
type Store a = M.Map a (Value a)

type Node a = Store a -> Store a -> Store a

type IONode a = Configurable IO (Store a) (Store a)


emptyStore :: Store a
emptyStore = M.empty


emptyNode :: Node a
emptyNode _ _ = emptyStore


configurePartition ::
  MonadFix m => ((asuper, bsuper) -> (aself, bself)) -> ((asuper, bsuper) -> ReaderT (aself, bself) m (asuper, bsuper)) -> bsuper -> ReaderT bself m bsuper
configurePartition final f b0 =
  ReaderT
    (\ b ->
      do
        (_, b') <- mfix (\ (a, _) -> g (a, b))
        return b')
  where
    g :: (aself, bself) -> m (aself, bself)
    g = fmap final . (runReaderT . mfix) (\ (a0, _) -> f (a0, b0))
            
      
  
  


-- Value
data Value a =
    String T.Text
  | Number Double
  | Bool Bool
  | Node (Node a)


instance ShowMy Value where
  showMy (String x) =
    show x
  
  showMy (Number x) =
    show x
    
  showMy (Bool x)   =
    show x
  
  showMy (Node _) =
    "<Node>"
  
    
unNode :: Value a -> Node a
unNode =
  go
    where
      go (Number x) =
        selfToNode (primitiveNumberSelf x)
        
      go (String x) =
        selfToNode (primitiveStringSelf x)
      
      go (Bool x) =
        selfToNode (primitiveBoolSelf x)
  
      go (Node c) =
        c
        
        
      
      
      selfToNode :: Monad m => m (Store a) -> Configurable m (Store a) (Store a)
      selfToNode m =
        EndoM (\ self0 ->
          M.union <$> m <*> pure self0)

    
-- Primitives
primitiveStringSelf :: Monad m => T.Text -> m (Store a)
primitiveStringSelf x =
  return emptyStore


primitiveNumberSelf :: Monad m => Double -> m (Store a)
primitiveNumberSelf x =
  return emptyStore


primitiveBoolSelf :: Monad m => Bool -> m (Store a)
primitiveBoolSelf x =
  return emptyStore


primitiveNumberUnop :: MonadThrow m => Unop -> Double -> m Value
primitiveNumberUnop Neg x =
  (return . Number . negate) x
  
primitiveNumberUnop s       _ =
  E.throwUndefinedNumberOp s


primitiveBoolUnop :: MonadThrow m => Unop -> Bool -> m Value
primitiveBoolUnop Not x =
  (return . Bool . not) x

primitiveBoolUnop s       _ =
  E.throwUndefinedBoolOp s


primitiveNumberBinop :: MonadThrow m => Binop -> Double -> Double -> m Value
primitiveNumberBinop Add x y =
  return . Number $ x + y

primitiveNumberBinop Sub x y =
  return . Number $ x - y

primitiveNumberBinop Prod x y =
  return . Number $ x * y

primitiveNumberBinop Div x y =
  return . Number $ x / y

primitiveNumberBinop Pow x y =
  return . Number $ x ** y

primitiveNumberBinop Lt x y =
  return . Bool $ x < y

primitiveNumberBinop Gt x y =
  return . Bool $ x > y

primitiveNumberBinop Eq x y =
  return . Bool $ x == y

primitiveNumberBinop Ne x y =
  return . Bool $ x /= y

primitiveNumberBinop Le x y =
  return . Bool $ x <= y

primitiveNumberBinop Ge x y =
  return . Bool $ x >= y

primitiveNumberBinop s _ _ =
  E.throwUndefinedNumberOp s


primitiveBoolBinop :: MonadThrow m => Binop -> Bool -> Bool -> m Value
primitiveBoolBinop And x y =
  return . Bool $ x && y

primitiveBoolBinop Or x y =
  return . Bool $ x || y

primitiveBoolBinop Lt x y =
  return . Bool $ x < y

primitiveBoolBinop Gt x y =
  return . Bool $ x > y

primitiveBoolBinop Eq x y =
  return . Bool $ x == y

primitiveBoolBinop Ne x y =
  return . Bool $ x /= y

primitiveBoolBinop Le x y =
  return . Bool $ x <= y

primitiveBoolBinop Ge x y =
  return . Bool $ x >= y

primitiveBoolBinop s _ _ =
  E.throwUndefinedBoolOp s


         
primitiveBindings :: Monad m => m (Store a)
primitiveBindings =
  return emptyStore
    
