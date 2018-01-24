{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Classes
  ( ShowMy(..)
  , ReadMy(..), readMy
  , MyError(..), throwMy, throwList
  ) where
  
import qualified Parser
import qualified Types.Parser as Parser
import qualified Expr
import qualified Types.Expr as Expr
import Types.Expr( Label )
import Types.Error

  
import Data.Char( showLitChar )
import Data.Foldable( foldr, asum )
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Functor.Identity
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Text.Parsec as P
import Control.Monad.Free
import Control.Monad.Trans
import Bound
  

-- | Extract a valid my-language source text representation from a
-- | Haskell data type representation
class ShowMy a where
  showMy :: a -> String
  showMy x = showsMy x ""
  
  showsMy :: a -> String -> String
  showsMy x s = showMy x ++ s
  
  
--class ShowMy1 m where
--  liftShowsMy :: (a -> String -> String) -> m a -> String -> String
  
  
-- | Print a literal string
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)
    
    
showLitText :: T.Text -> String -> String
showLitText = showLitString . T.unpack


instance ShowMy Label where showsMy = (++) . T.unpack


instance ShowMy Parser.Symbol where showsMy (Parser.S s) = showChar '\'' . showsMy s


instance ShowMy Parser.Tag where
  showsMy (Parser.Label l) = showChar '.' . showsMy l
  showsMy (Parser.Symbol s) = showChar '.' . showChar '(' . showsMy s . showChar ')'
    
    
instance (ShowMy a, ShowMy (f (Free f a))) => ShowMy (Free f a) where
  showMy (Pure a) = showMy a
  showMy (Free f) = showMy f

  
instance ShowMy Parser.Var where
  showsMy (Parser.Pub t) = showsMy t
  showsMy (Parser.Priv l) = showsMy l
  
  
instance ShowMy Parser.Syntax where
  showsMy e = case e of
    Parser.IntegerLit n -> shows n
    Parser.NumberLit n  -> shows n
    Parser.StringLit x  -> showChar '"' . showLitText x . showChar '"'
    Parser.Var x        -> showsMy x
    Parser.Get path     -> showsMy path
    Parser.Block xs     -> showBlock xs
    Parser.Extend e xs  -> showParen t (showsMy e) . showChar ' ' . showBlock xs where
      t = case e of Parser.Unop{} -> True; Parser.Binop{} -> True; _ -> False
    Parser.Unop o a     -> showsMy o . showParen t (showsMy a)  where 
      t = case a of Parser.Binop{} -> True; _ -> False
    Parser.Binop o a b  -> showArg a . showChar ' ' . showsMy o
      . showChar ' ' . showArg b where
        showArg a = showParen t (showsMy a) where 
          t = case a of Parser.Binop p _ _ -> Parser.prec p o; _ -> False
    where
      showBlock [] = showString "{}"
      showBlock (x:xs) = showString "{ " . showsMy x
        . flip (foldr showStmt) xs . showString " }"
    
      showStmt a = showString "; " . showsMy a
      
      
instance ShowMy Parser.Unop where
  showsMy Parser.Neg   = showChar '-'
  showsMy Parser.Not   = showChar '!'

  
instance ShowMy Parser.Binop where
  showsMy Parser.Add   = showChar '+'
  showsMy Parser.Sub   = showChar '-'
  showsMy Parser.Prod  = showChar '*'
  showsMy Parser.Div   = showChar '/'
  showsMy Parser.Pow   = showChar '^'
  showsMy Parser.And   = showChar '&'
  showsMy Parser.Or    = showChar '|'
  showsMy Parser.Lt    = showChar '<'
  showsMy Parser.Gt    = showChar '>'
  showsMy Parser.Eq    = showString "=="
  showsMy Parser.Ne    = showString "!="  
  showsMy Parser.Le    = showString "<="
  showsMy Parser.Ge    = showString ">="
  
  
instance ShowMy a => ShowMy (Parser.Field a) where
  showsMy (b `Parser.At` t) = showsMy b . showsMy t
    
    
instance ShowMy Parser.Stmt where
  showsMy (Parser.SetPun l)  = showsMy l
  showsMy (l `Parser.Set` r) = showsMy l . showString " = " . showsMy r

  
instance ShowMy Parser.SetExpr where
  showsMy e = case e of
    Parser.SetPath x -> showsMy x
    Parser.SetBlock xs -> showBlock xs
    Parser.SetDecomp l xs -> showsMy l . showChar ' '
      . showBlock xs
    where
      showBlock []      = showString "{}"
      showBlock (x:xs)  = showString "{ " . showsMy x
        . flip (foldr showStmt) xs . showString " }"
      showStmt a = showString "; " . showsMy a
      
      
instance ShowMy Parser.MatchStmt where
  showsMy (r `Parser.Match` l) = showsMy r . showString " = " . showsMy l
  showsMy (Parser.MatchPun l)  = showsMy l
  
  
instance ShowMy (NonEmpty Parser.Stmt) where
  showsMy (x:|xs) = showsMy x  . flip (foldr showsStmt) xs
    where
      showsStmt a = showString ";\n\n" . showsMy a
      
      
instance (ShowMy k, ShowMy a) => ShowMy (Expr.Expr s k a) where
  showsMy (Expr.String t)       = shows t
  showsMy (Expr.Number d)       = shows d
  showsMy (Expr.Var a)          = showsMy a
  showsMy (Expr.Block{})        = error "showMy: Expr.Block"
  showsMy (e `Expr.At` t)       = showsMy e . showsMy t
  showsMy (e `Expr.Fix` x)      = error "showMy: Expr.Fix"
  showsMy (e1 `Expr.Update` e2) = error "showMy: Expr.Update"
  showsMy (e `Expr.AtPrim` p)   = error "showMy: Expr.AtPrim"
    
    
instance ShowMy k => ShowMy (Expr.Key k) where
  showsMy (Expr.Label l) = showChar '.' . showsMy l
  showsMy (Expr.Symbol s) = showChar '.' . showChar '(' . showsMy s . showChar ')'
  showsMy Expr.Self = error "showMy: Expr.Self"
  showsMy (Expr.Unop _) = error "showMy: Expr.Unop"
  showsMy (Expr.Binop _) = error "showMy: Expr.Binop"
  
  
-- | Parse source text into a my-language Haskell data type
class ReadMy a where readsMy :: Parser.SymParser a
  
  
readMy :: ReadMy a => String -> a
readMy = either (error "readMy") id . P.runParser (readsMy <* P.eof) minBound "readMy" . T.pack


readIOMy :: ReadMy a => String -> IO a
readIOMy = either (ioError . userError . displayError) return . P.runParser (readsMy <* P.eof) minBound "readMy" . T.pack

              
instance ReadMy Parser.Syntax where readsMy = Parser.rhs

    
instance ReadMy Parser.Stmt where readsMy = Parser.stmt


instance ReadMy Parser.SetExpr where readsMy = Parser.lhs


instance ReadMy Parser.MatchStmt where readsMy = Parser.matchstmt


instance ReadMy (Expr.Expr Expr.ListO (Expr.Key Parser.Symbol) Parser.Var) where
  readsMy = do
    e <- readsMy
    either
      (P.unexpected . show)
      return
      (Expr.expr e)
      
      
-- | Class for displaying exceptions
class MyError a where
  displayError :: a -> String
  
  
throwMy :: MyError a => a -> IO b
throwMy = ioError . userError . displayError


throwList :: (MyError a, Functor t, Foldable t) => t a -> IO b
throwList = asum . fmap throwMy


instance MyError Expr.ScopeError where
  displayError (Expr.ParamFree v) = "Not in scope: Variable " ++ showMy v
  displayError (Expr.SymbolFree s) = "Not in scope: Symbol " ++ showMy s
  

instance MyError Expr.ExprError where
  displayError e = case e of
    Expr.OlappedMatch perr -> "Overlapping destructuring of paths: \n" ++
      unlines (showMy <$> Expr.listPaths perr)
      
    Expr.OlappedSet v perr -> "Overlapping definitions for paths: \n" ++
      unlines (showMy <$> Expr.listPaths perr)
      
    Expr.OlappedSym s -> "Multiple definitions for symbol " ++ showMy s
      
      
instance MyError P.ParseError where
  displayError p = shows "Parse error: " (show p)
  
  
instance MyError IOError where
  displayError e = shows "IO error: " (show e)
    
