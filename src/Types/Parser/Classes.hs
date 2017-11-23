{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Parser.Classes
  ( ShowMy(..)
  , ReadMy(..)
  ) where
  
import Parser
import Types.Parser
  
  
import Data.Char( showLitChar )
import Data.Foldable( foldr )
import Data.List.NonEmpty( NonEmpty(..) )
import qualified Data.Text as T
import Text.Parsec.Text( Parser )
import Control.Monad.Free
import Control.Monad.Trans
  

-- | Extract a valid my-language source text representation from a
-- | Haskell data type representation
class ShowMy a where
  showMy :: a -> String
  showMy x = showsMy x ""
  
  showsMy :: a -> String -> String
  showsMy x s = showMy x ++ s
  
  
-- | Print a literal string
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)
    
    
showLitText :: T.Text -> String -> String
showLitText = showLitString . T.unpack


instance ShowMy Tag where showsMy x s = showLitText x s
    
    
instance (ShowMy a, ShowMy (f (Free f a))) => ShowMy (Free f a) where
  showMy (Pure a) = showMy a
  showMy (Free f) = showMy f

  
instance ShowMy a => ShowMy (Vis a) where
  showsMy (Pub a)   s = "." ++ showsMy a s
  showsMy (Priv a)  s = showsMy a s
  
  
instance ShowMy a => ShowMy (Expr a) where
  showsMy (IntegerLit n)        s = show n ++ s
  showsMy (NumberLit n)         s = show n ++ s
  showsMy (StringLit x)         s = showLitText x s
  showsMy (Var x)               s = showsMy x s
  showsMy (Get path)            s = showsMy path s
  showsMy (Block [])            s = "{}" ++ s
  showsMy (Block (x:xs))        s =
    "{ " ++ showsMy x (foldr showsStmt (" }" ++ s) xs)
    where
      showsStmt a x = "; " ++ showsMy a x
  showsMy (Update a b)          s = showsVal a (showsParens b s)
    where
      showsParens a             s = "(" ++ showsMy a (")" ++ s)
      showsVal a@(Unop{})       s = showsParens a s
      showsVal a@(Binop{})      s = showsParens a s
      showsVal a                s = showsMy a s
  showsMy (Unop o a)            s = showsMy o (showsOp a s)
    where 
      showsOp a@(Binop{}) s = "(" ++ showsMy a (")" ++ s)
      showsOp a                 s = showsMy a s
  showsMy (Binop o a b)         s =
    showsOp a (" " ++ showsMy o (" " ++ showsOp b s))
    where
      showsOp a@(Binop p _ _) s 
        | prec p o    = "(" ++ showsMy a (")" ++ s)
        | otherwise   = showsMy a s
      showsOp a               s = showsMy a s
      
      
instance ShowMy Unop where
  showsMy Neg   = showLitChar '-'
  showsMy Not   = showLitChar '!'

  
instance ShowMy Binop where
  showsMy Add   = showLitChar '+'
  showsMy Sub   = showLitChar '-'
  showsMy Prod  = showLitChar '*'
  showsMy Div   = showLitChar '/'
  showsMy Pow   = showLitChar '^'
  showsMy And   = showLitChar '&'
  showsMy Or    = showLitChar '|'
  showsMy Lt    = showLitChar '<'
  showsMy Gt    = showLitChar '>'
  showsMy Eq    = showLitString "=="
  showsMy Ne    = showLitString "!="  
  showsMy Le    = showLitString "<="
  showsMy Ge    = showLitString ">="
  
  
instance ShowMy a => ShowMy (Field a) where
  showsMy (a `At` x) s = showsMy a ("." ++ showsMy x s)
    
    
instance ShowMy a => ShowMy (Stmt a) where
  showMy (Declare l)  = showMy  l ++ " ="
  showMy (SetPun l)   = showMy l
  showMy (l `Set` r)  = showMy l ++ " = " ++  showMy r

  
instance ShowMy a => ShowMy (SetExpr a) where
  showMy (SetPath x)        = showMy x
  showMy (SetBlock [])      = "{}"
  showMy (SetBlock (x:xs))  =
    "{ " ++ showMy x ++ foldr showsStmt " }" xs
    where
      showsStmt a x = "; " ++ showsMy a x
  showMy (SetConcat stmts l) =
    "[" ++ showsBlock stmts (showsTail l "]")
    where
      showsTail a       s = "| " ++ showsMy a (" " ++ s)
      
      showsBlock []     s = s
      showsBlock (x:xs) s =
        " { " ++ showsMy x (foldr showsStmts (" } " ++ s) xs)
        
      showsStmts a      x = "; " ++ showsMy a x
      
      
instance ShowMy a => ShowMy (MatchStmt a) where
  showMy (r `Match` l)  = showMy r ++ " = " ++ showMy l
  showMy (MatchPun l)   = showMy l
  
  
instance ShowMy a => ShowMy (NonEmpty (Stmt a)) where
  showsMy (x:|xs) s = showsMy x (foldr showsStmt s xs)
    where
      showsStmt a x = ";\n\n" ++ showsMy a x
  
  
  
-- | Parse source text into a my-language Haskell data type
class ReadMy a where readsMy :: Parser a
  
readMy :: ReadMy a => String -> a
readMy = either (error "readMy") id . readParser readsMy


showReadMy :: (ReadMy a, ShowMy a) => a -> String
showReadMy e = "readMy" ++ show (showMy e)

              
instance ReadMy (Expr (Vis Tag)) where readsMy = rhs
instance Show (Expr (Vis Tag)) where show = showReadMy

    
instance ReadMy (Stmt (Vis Tag)) where readsMy = stmt
instance Show (Stmt (Vis Tag)) where show = showReadMy


instance ReadMy (SetExpr (Vis Tag)) where readsMy = lhs
instance Show (SetExpr (Vis Tag)) where show = showReadMy


instance ReadMy (MatchStmt (Vis Tag)) where readsMy = matchstmt
instance Show (MatchStmt (Vis Tag)) where show = showReadMy

  
