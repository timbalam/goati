{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Classes
  ( ShowMy(..)
  , ReadMy(..)
  ) where
  
import qualified Parser
import qualified Types.Parser as Parser
import qualified Core
import qualified Types.Core as Core
import Types.Core( Vis(..), Tag )
  
  
import Data.Char( showLitChar )
import Data.Foldable( foldr )
import Data.List.NonEmpty( NonEmpty(..) )
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
  
  
instance ShowMy a => ShowMy (Parser.Expr a) where
  showsMy (Parser.IntegerLit n)        s = show n ++ s
  showsMy (Parser.NumberLit n)         s = show n ++ s
  showsMy (Parser.StringLit x)         s = showLitText x s
  showsMy (Parser.Var x)               s = showsMy x s
  showsMy (Parser.Get path)            s = showsMy path s
  showsMy (Parser.Block [] Nothing)    s = "{}" ++ s
  showsMy (Parser.Block [] (Just e))   s = "{... " ++ showsMy e (" }" ++ s)
  showsMy (Parser.Block (x:xs) m)      s =
    "{ " ++ showsMy x (foldr showsStmt (showsTail m (" }" ++ s)) xs)
    where
      showsStmt a x = "; " ++ showsMy a x
      showsTail Nothing x = x
      showsTail (Just e) x = " ... " ++ showsMy e x
  showsMy (Parser.Update a b)          s = showsVal a (showsParens b s)
    where
      showsParens a               s = "(" ++ showsMy a (")" ++ s)
      showsVal a@(Parser.Unop{})  s = showsParens a s
      showsVal a@(Parser.Binop{}) s = showsParens a s
      showsVal a                  s = showsMy a s
  showsMy (Parser.Unop o a)            s = showsMy o (showsOp a s)
    where 
      showsOp a@(Parser.Binop{})  s = "(" ++ showsMy a (")" ++ s)
      showsOp a                   s = showsMy a s
  showsMy (Parser.Binop o a b)         s =
    showsOp a (" " ++ showsMy o (" " ++ showsOp b s))
    where
      showsOp a@(Parser.Binop p _ _) s 
        | Parser.prec p o = "(" ++ showsMy a (")" ++ s)
        | otherwise       = showsMy a s
      showsOp a                      s = showsMy a s
      
      
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
  
  
instance ShowMy a => ShowMy (Parser.Field a) where
  showsMy (a `Parser.At` x) s = showsMy a ("." ++ showsMy x s)
    
    
instance ShowMy a => ShowMy (Parser.Stmt a) where
  showMy (Parser.Declare l)  = showMy  l ++ " ="
  showMy (Parser.SetPun l)   = showMy l
  showMy (l `Parser.Set` r)  = showMy l ++ " = " ++  showMy r

  
instance ShowMy a => ShowMy (Parser.SetExpr a) where
  showsMy (Parser.SetPath x)              s = showsMy x s
  showsMy (Parser.SetBlock [] Nothing)    s = "{}" ++ s
  showsMy (Parser.SetBlock [] (Just e))   s = "{... " ++ showsMy e (" }" ++ s)
  showsMy (Parser.SetBlock (x:xs) m)      s =
    "{ " ++ showsMy x (foldr showsStmt (showsTail m (" }" ++ s)) xs)
    where
      showsStmt a x = "; " ++ showsMy a x
      showsTail Nothing x = x
      showsTail (Just e) x = " ... " ++ showsMy e x
      
      
instance ShowMy a => ShowMy (Parser.MatchStmt a) where
  showMy (r `Parser.Match` l)  = showMy r ++ " = " ++ showMy l
  showMy (Parser.MatchPun l)   = showMy l
  
  
instance ShowMy a => ShowMy (NonEmpty (Parser.Stmt a)) where
  showsMy (x:|xs) s = showsMy x (foldr showsStmt s xs)
    where
      showsStmt a x = ";\n\n" ++ showsMy a x
      
      
liftShows :: (a -> String -> String) -> Core.Expr a -> String -> String
liftShows shows (Core.String t)       s = show t ++ s
liftShows shows (Core.Number d)       s = show d ++ s
liftShows shows (Core.Var a)          s = shows a s
liftShows shows Core.Undef            s = s
liftShows shows (Core.Block{})        s = "<Node>" ++ s
liftShows shows (e `Core.At` x)       s = liftShows shows e ("." ++ showsMy x s)
liftShows shows (e `Core.Fix` x)      s = liftShows shows e ("~" ++ showsMy x s)
liftShows shows (e1 `Core.Update` e2) s =
  liftShows shows e1 ("(" ++ liftShows shows e2 (")" ++ s))
  
  
instance ShowMy a => ShowMy (Core.Expr a) where
  showsMy = liftShows showsMy
  
  
instance ShowMy a => ShowMy (Maybe (Vis a)) where
  showsMy Nothing   s = s
  showsMy (Just v)  s = showsMy v s
  
  
-- | Parse source text into a my-language Haskell data type
class ReadMy a where readsMy :: Parser a
  
readMy :: ReadMy a => String -> a
readMy = either (error "readMy") id . P.parse (readsMy <* P.eof) "myi" . T.pack


showReadMy :: (ReadMy a, ShowMy a) => a -> String
showReadMy e = "readMy " ++ show (showMy e)

              
instance ReadMy (Parser.Expr (Vis Tag)) where readsMy = Parser.rhs

    
instance ReadMy (Parser.Stmt (Vis Tag)) where readsMy = Parser.stmt


instance ReadMy (Parser.SetExpr (Vis Tag)) where readsMy = Parser.lhs


instance ReadMy (Parser.MatchStmt (Vis Tag)) where readsMy = Parser.matchstmt


instance ReadMy (Core.Expr (Vis Tag)) where
  readsMy = do
    e <- readsMy
    maybe
      (P.unexpected "expr") 
      return
      (Core.getresult (Core.expr e))

