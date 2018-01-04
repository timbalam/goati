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
import Types.Expr( Sym(..), Vis(..), Tag(..), Label )
import Types.Error
  
  
import Data.Char( showLitChar )
import Data.Foldable( foldr, asum )
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Functor.Identity
import qualified Data.Text as T
import qualified Data.Map as M
import Text.Parsec.Text( Parser )
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


instance ShowMy a => ShowMy (Tag a) where
  showsMy (Label l) s = showsMy l s
  showsMy (Id a)    s = "(" ++ showsMy a (")" ++ s)
    
    
instance (ShowMy a, ShowMy (f (Free f a))) => ShowMy (Free f a) where
  showMy (Pure a) = showMy a
  showMy (Free f) = showMy f

  
instance ShowMy a => ShowMy (Vis a) where
  showsMy (Pub t)   s = "." ++ showsMy t s
  showsMy (Priv l)  s = showsMy l s
  
  
instance ShowMy a => ShowMy (Sym a) where
  showsMy (Intern t) s = showsMy t s
--showsMy (Extern p) s = "#\"" ++ showLitString p ("\"" ++ s)
  
  
instance ShowMy Parser.Syntax where
  showsMy e = case e of
    Parser.IntegerLit n -> showString (show n)
    Parser.NumberLit n  -> showString (show n)
    Parser.StringLit x  -> showString "\""
      . showLitText x . showString "\""
    Parser.Var x        -> showsMy x
    Parser.Get path     -> showsMy path
    Parser.Block xs     -> showBlock xs
    Parser.Extend e xs  -> showVal e . showString " " . showBlock xs
    Parser.Unop o a     -> showsMy o . showOp a  where 
      showOp a@(Parser.Binop{})  = showString "(" . showsMy a . showString ")"
      showOp a                   = showsMy a
    Parser.Binop o a b  -> showOp a . showString " "
      . showsMy o . showString " " . showOp b where
      showOp a@(Parser.Binop p _ _) 
        | Parser.prec p o = showString "(" . showsMy a
          . showString ")"
      showOp a            = showsMy a
    where
      showBlock [] = showString "{}"
      showBlock (x:xs) = showString "{ " . showsMy x
        . flip (foldr showStmt) xs . showString " }"
    
      showStmt a = showString "; " . showsMy a
      showParens a = showString "(" . showsMy a . showString ")"
      showVal a@(Parser.Unop{})  = showParens a
      showVal a@(Parser.Binop{}) = showParens a
      showVal a                  = showsMy a
      
      
instance ShowMy Parser.Unop where
  showsMy Parser.Neg   = showLitChar '-'
  showsMy Parser.Not   = showLitChar '!'

  
instance ShowMy Parser.Binop where
  showsMy Parser.Add   = showLitChar '+'
  showsMy Parser.Sub   = showLitChar '-'
  showsMy Parser.Prod  = showLitChar '*'
  showsMy Parser.Div   = showLitChar '/'
  showsMy Parser.Pow   = showLitChar '^'
  showsMy Parser.And   = showLitChar '&'
  showsMy Parser.Or    = showLitChar '|'
  showsMy Parser.Lt    = showLitChar '<'
  showsMy Parser.Gt    = showLitChar '>'
  showsMy Parser.Eq    = showLitString "=="
  showsMy Parser.Ne    = showLitString "!="  
  showsMy Parser.Le    = showLitString "<="
  showsMy Parser.Ge    = showLitString ">="
  
  
instance (ShowMy a, ShowMy b) => ShowMy (Parser.Field a b) where
  showsMy (b `Parser.At` t) = showsMy b . showString "." . showsMy t
    
    
instance ShowMy Parser.Stmt where
  showMy (Parser.SetPun l)   = showMy l
  showMy (l `Parser.Set` r)  = showMy l ++ " = " ++  showMy r

  
instance ShowMy Parser.SetExpr where
  showsMy e = case e of
    Parser.SetPath x -> showsMy x
    Parser.SetBlock xs -> showBlock xs
    Parser.SetDecomp l xs -> showsMy l . showString " "
      . showBlock xs
    where
      showBlock []      = showString "{}"
      showBlock (x:xs)  = showString "{ " . showsMy x
        . flip (foldr showStmt) xs . showString " }"
      showStmt a = showString "; " . showsMy a
      
      
instance ShowMy Parser.MatchStmt where
  showMy (r `Parser.Match` l)  = showMy r ++ " = " ++ showMy l
  showMy (Parser.MatchPun l)   = showMy l
  
  
instance ShowMy (NonEmpty Parser.Stmt) where
  showsMy (x:|xs) s = showsMy x (foldr showsStmt s xs)
    where
      showsStmt a x = ";\n\n" ++ showsMy a x
      
      
instance ShowMy a => ShowMy (Expr.Eval a) where
  showsMy (Expr.Eval (Right e))  s = showsMy e s
  showsMy (Expr.Eval (Left a))   _ = error ("showMy: not in scope: " ++ showMy a)
      
      
instance ShowMy a => ShowMy (Expr.Expr a) where
  showsMy (Expr.String t)       s = show t ++ s
  showsMy (Expr.Number d)       s = show d ++ s
  showsMy (Expr.Var a)          s = showsMy a s
  showsMy (Expr.Block{})        _ = error "showMy: Block"
  showsMy (e `Expr.At` t)       s = showsMy e ("." ++ showsMy t s)
  showsMy (e `Expr.Fix` x)      _ = error "showMy: Fix"
  showsMy (e1 `Expr.Update` e2) s =
    showsMy e1 ("(" ++ showsMy e2 (")" ++ s))
    
    
instance ShowMy Expr.Id
  
  
-- | Parse source text into a my-language Haskell data type
class ReadMy a where readsMy :: Parser a
  
  
readMy :: ReadMy a => String -> a
readMy = either (error "readMy") id . P.parse (readsMy <* P.eof) "readMy" . T.pack


readIOMy :: ReadMy a => String -> IO a
readIOMy = either (ioError . userError . displayError . ParseError) return . P.parse (readsMy <* P.eof) "readMy" . T.pack

              
instance ReadMy Parser.Syntax where readsMy = Parser.rhs

    
instance ReadMy Parser.Stmt where readsMy = Parser.stmt


instance ReadMy Parser.SetExpr where readsMy = Parser.lhs


instance ReadMy Parser.MatchStmt where readsMy = Parser.matchstmt


instance ReadMy (Expr.Expr (Sym (Vis Expr.Id))) where
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


instance ShowMy a => MyError (EvalError a) where
  displayError e = case e of
    LookupFailed a -> "Field not present: " ++ showMy a
    ParamUndefined x -> "Not defined: " ++ showMy x
    
    
instance ShowMy a => MyError (ScopeError a) where
  displayError (ParamFree a) = "Not in scope: " ++ showMy a
  

instance (ShowMy a, ShowMy b) => MyError (ExprError a b) where
  displayError e = case e of
    OlappedMatch perr -> "Overlapping paths in destructuring: \n" ++
      unlines (showMy <$> listPaths perr)
      
    OlappedSet perr -> "Overlapping paths in definition: \n" ++
      unlines (showMy <$> listPaths perr)
      
      
instance MyError ParseError where
  displayError = shows "parse: " . show
  
  
instance MyError ImportError where
  displayError = shows "import: " . show
    
