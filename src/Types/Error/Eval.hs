{-# LANGUAGE FlexibleContexts #-}

module Types.Error.Eval
  where
import Control.Monad.Catch( MonadThrow, throwM )
import Control.Exception
import Data.Map as M
import Data.Typeable

import Text.Parsec( ParseError )

-- Error
data UnboundVar k = UnboundVar k String
  deriving Typeable
instance Show k => Show (UnboundVar k) where
  show (UnboundVar k msg) = msg ++ ": " ++ show k
instance (Show k, Typeable k) => Exception (UnboundVar k)
  
data OverlappingDefn k = OverlappingDefn k String
  deriving Typeable
instance Show k => Show (OverlappingDefn k) where
  show (OverlappingDefn k msg) = msg ++ ": " ++ show k
instance (Show k, Typeable k) => Exception (OverlappingDefn k)

throwUnboundVarIn :: (Show k, Typeable k, MonadThrow m) => k -> M.Map k v -> m a
throwUnboundVarIn k x = throwM (UnboundVar k ("Unbound var in "++show (show <$> M.keys x)))

throwUnboundVar :: (Show k, Typeable k, MonadThrow m) => k -> m a
throwUnboundVar k = throwM (UnboundVar k "Unbound var")

throwOverlappingDefn :: (Show k, Typeable k, MonadThrow m) => k -> m a
throwOverlappingDefn k = throwM (OverlappingDefn k "Overlapping definitions for var")

data PrimitiveType = NumberType | BoolType | StringType
  deriving Typeable
data UndefinedPrimOp k = UndefinedPrimOp PrimitiveType k String
  deriving Typeable
  
  
instance Show k => Show (UndefinedPrimOp k) where
  show (UndefinedPrimOp _ k msg) = msg ++ ": " ++ show k
instance (Show k, Typeable k) => Exception (UndefinedPrimOp k)

throwUndefinedNumberOp :: (MonadThrow m, Show s, Typeable s) => s -> m a
throwUndefinedNumberOp s = throwM (UndefinedPrimOp NumberType s "Operation undefined for numbers")

throwUndefinedBoolOp :: (MonadThrow m, Show s, Typeable s) => s -> m a
throwUndefinedBoolOp s = throwM (UndefinedPrimOp BoolType s "Operation undefined for booleans")

throwUndefinedStringOp :: (MonadThrow m, Show s, Typeable s) => s -> m a
throwUndefinedStringOp s = throwM (UndefinedPrimOp StringType s "Operation undefined for strings")

data Parser = Parser ParseError String
  deriving Typeable
instance Show Parser where
  show (Parser e msg) = msg ++ ": " ++ show e
instance Exception Parser

throwParseError :: MonadThrow m => ParseError -> m a
throwParseError e = throwM (Parser "parse error" e)

data ImportError k = ImportError k String
  deriving Typeable
instance Show k => Show (ImportError k) where
  show (ImportError String k) = msg ++ ": " ++ show k
instance (Show k, Typeable k) => Exception (ImportError k)

throwImportError :: (MonadThrow m, Show k, Typeable k) => k -> m a
throwImportError k = throwM (ImportError k "Import error")

newtype Missing = Missing String
  deriving Typeable
instance Show Missing where
  show (Missing msg) = msg
instance Exception Missing

throwMissingError :: MonadThrow m => m a
throwMissingError = throwM (Missing "Missing result")

