{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes, UndecidableInstances #-}
module Parser
  ( decfloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , path
  , pathexpr
  , program, showProgram
  , Parser, parse
  , ShowMy(..)
  , ReadMy(..)
  )
  where
  
import Types.Parser

import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec
  ( (<|>)
  , (<?>)
  , try
  , parse
  )
import Text.Parsec.Text( Parser )
import Numeric( readHex, readOct )
import Control.Applicative( liftA2 )
import Data.Char( showLitChar )
import Data.Foldable( foldl', concat, toList )
import Data.List.NonEmpty( NonEmpty(..), nonEmpty )
import Data.Semigroup( (<>) )
import Data.Function( (&) )
import Data.Bifunctor( bimap )
--import Control.Monad.Free
import Control.Monad.State


-- | Extract a valid my-language source text representation from a
-- | Haskell data type representation
class ShowMy a where
  showMy :: a -> String
  showMy x = showsMy x ""
  
  showsMy :: a -> String -> String
  showsMy x s = showMy x ++ s
  

showSep :: ShowMy a => String -> a -> ShowS
showSep sep a = showString sep . showsMy a


-- | Utility functions for printing string literals
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)
    
    
showLitText :: T.Text -> String -> String
showLitText = showLitString . T.unpack


showText :: T.Text -> ShowS
showText = (++) . T.unpack

   
-- | Parse source text into a my-language Haskell data type
class ReadMy a where readsMy :: Parser a

  
readMy :: ReadMy a => String -> a
readMy = either (errorWithoutStackTrace "readMy") id . parse (readsMy <* P.eof) "readMy" . T.pack


readIOMy :: ReadMy a => String -> IO a
readIOMy = either (ioError . userError . show) return
  . parse (readsMy <* P.eof) "readMy" . T.pack

     
      
-- | Parse a comment
comment :: Parser T.Text
comment = do
  try (P.string "//")
  s <- P.manyTill P.anyChar (try ((P.endOfLine >> return ()) <|> P.eof))
  return (T.pack s)
    
    
-- | Parse whitespace and comments
spaces :: Parser ()
spaces = P.spaces >> P.optional (comment >> spaces) 

    
-- | Parse any valid numeric literal
number :: Parser (Expr k a)
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number")
    <* spaces
    
    
-- | Parse a valid binary number
binary :: Parser (Expr k a)
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: Parser (Expr k a)
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: Parser (Expr k a)
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
  
  
  
-- | Parse a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
  
  
-- | Parse a single decimal point / field accessor (disambiguated from extension dots)
point :: Parser Char
point = try (P.char '.' <* P.notFollowedBy (P.char '.'))
    
    
-- | Parser for valid decimal or floating point number
decfloat :: Parser (Expr k a)
decfloat =
  prefixed
    <|> unprefixed
  where
    prefixed =
      do
        try (P.string "0d")
        IntegerLit . read <$> integer P.digit
        
    unprefixed =
      do
        xs <- integer P.digit
        fracnext xs                             -- int frac
                                                -- int frac exp
          <|> expnext xs                        -- int exp
          <|> (return . IntegerLit) (read xs)   -- int
          
    fracnext xs =
      do 
        y <- point
        m <- P.optionMaybe (integer P.digit)
        case m of
          Nothing ->
            -- frac
            (return . NumberLit . read) (xs ++ [y, '0'])
            
          Just ys ->
            expnext (xs ++ [y] ++ ys)   -- frac exp
              <|>
                (return . NumberLit . read) (xs ++ [y] ++ ys)
                                      -- frac
          
    expnext xs =
      do 
        e <- P.oneOf "eE"
        sgn <- P.option [] (P.oneOf "+-" >>= return . pure)
        ys <- integer P.digit
        (return . NumberLit . read) (xs ++ e:sgn ++ ys)


-- | Parse a double-quote wrapped string literal
string :: Parser (Expr k a)
string =
  StringLit . T.pack <$> stringfragment

  
stringfragment :: Parser String
stringfragment =
  P.between
    (P.char '"')
    (P.char '"' >> spaces)
    (P.many (P.noneOf "\"\\" <|> escapedchars))

    
-- | Parse an escaped character
escapedchars :: Parser Char
escapedchars =
  do
    P.char '\\'
    x <- P.oneOf "\\\"nrt"
    return
      (case x of
        '\\' ->
          x
          
        '"'  ->
          x
          
        'n'  ->
          '\n'
      
        'r'  ->
          '\r'
        
        't'  ->
          '\t')

          
          
-- | Parse a valid identifier string
instance ReadMy Ident where
  readsMy = do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    (return . T.pack) (x:xs)

  
instance ShowMy Ident where
  showsMy = showText
    

identpath :: Parser String
identpath =
  do
    x <- P.letter
    xs <- rest
    spaces
    return (x:xs)
  where
    rest = 
      alphanumnext <|> slashnext <|> return []
        
    alphanumnext = do
      x <- P.alphaNum
      xs <- rest
      return (x:xs)
      
    slashnext = do
      (c,x) <- try ((,) <$> P.char '/' <*> P.letter)
      xs <- rest
      return (c:x:xs)
      
      
-- | Parse a symbol
instance ReadMy Symbol where 
  readsMy = P.char '\'' >> S_ <$> readsMy
    
  
instance ShowMy Symbol where
  showsMy (S_ s) = showChar '\'' . showText s

  
-- | Parse a valid field accessor
instance ReadMy a => ReadMy (Key a) where
  readsMy = do
    point
    spaces
    (Symbol <$> parens readsMy)
      <|> (Ident <$> readsMy)
      
      
instance ShowMy a => ShowMy (Key a) where 
  showsMy (Ident l) = showChar '.' . showsMy l
  showsMy (Symbol s) = showChar '.' . showChar '(' . showsMy s . showChar ')'
      
    
-- | Parse an address path
instance (ReadMy a, ReadMy b) => ReadMy (Field a b) where
  readsMy = liftA2 At readsMy readsMy

  
instance (ShowMy a, ShowMy b) => ShowMy (Field a b) where
  showsMy (a `At` t) = showsMy a . showsMy t
        
        
instance (ReadMy a, ReadMy b) => ReadMy (Path a b) where
  readsMy = readsMy >>= path


instance (ShowMy b, ShowMy (Field a (Path a b))) => ShowMy (Path a b) where
  showsMy (Pure a) = showsMy a
  showsMy (Free f) = showsMy f
  

path :: ReadMy a => b -> Parser (Path a b)
path = rest . Pure
  where
    rest x =
      (readsMy >>= rest . Free . At x)
        <|> return x
        
       
-- | Parse a variable
instance (ReadMy a, ReadMy b) => ReadMy (Vis a b) where
  readsMy =
    (Pub <$> readsMy)
      <|> (Priv <$> readsMy)

      
instance (ShowMy a, ShowMy b) => ShowMy (Vis a b) where
  showsMy (Priv l) = showsMy l
  showsMy (Pub t) = showsMy t


-- | Parse a full precedence expression
instance ReadMy Syntax where
  readsMy =
    orexpr    -- '!' ...
              -- '-' ...
              -- '"' ...
              -- '(' ...
              -- digit ...
              -- '{' ...
              -- '.' alpha ...
              -- alpha ...
              
              
instance (ShowMy k, ShowMy a) => ShowMy (Expr k a) where
  showsMy e = case e of
    IntegerLit n  -> shows n
    NumberLit n   -> shows n
    StringLit x   -> showChar '"' . showLitText x . showChar '"'
    Var x         -> showsMy x
    Get p         -> showsMy p
    Block b       -> showsMy b
    Extend e b    -> showParen t (showsMy e) . showChar ' ' . showsMy b where
      t = case e of Unop{} -> True; Binop{} -> True; _ -> False
    Unop o a      -> showUnop o . showParen t (showsMy a)  where 
      t = case a of Binop{} -> True; _ -> False
    Binop o a b   -> showArg a . showChar ' ' . showBinop o
      . showChar ' ' . showArg b where
        showArg a = showParen t (showsMy a) where 
          t = case a of Binop p _ _ -> prec p o; _ -> False
          
          
-- | Parse binary operations observing operator precedence
orexpr :: Parser Syntax
orexpr =
  P.chainl1 andexpr (Binop <$> readOr)

      
andexpr :: Parser Syntax
andexpr =
  P.chainl1 cmpexpr (Binop <$> readAnd)

        
cmpexpr :: Parser Syntax
cmpexpr =
  do
    a <- addexpr
    (do
       s <- op
       b <- addexpr
       return (s a b))
      <|> return a
  where
    op = Binop <$> (readGt <|> readLt <|> readEq <|> readNe <|> readGe <|> readLe)
   
   
addexpr :: Parser Syntax
addexpr =
  P.chainl1 mulexpr (Binop <$> (readAdd <|> readSub))


mulexpr :: Parser Syntax
mulexpr =
  P.chainl1 powexpr (Binop <$> (readProd <|> readDiv))


powexpr :: Parser Syntax
powexpr =
  P.chainl1 term (Binop <$> readPow)
    where
      term =
        unop            -- '!'
                        -- '-'
          <|> pathexpr  -- '"'
                        -- '('
                        -- digit
                        -- '{'
                        -- '.'
                        -- alpha
          
-- | Parse an unary operation
unop :: Parser Syntax
unop = Unop <$> op <*> pathexpr
  where
    op = 
      readNeg       -- '-' ...
        <|> readNot -- '!' ...
        
        
-- | Parse a right-hand side chain of field accesses and extensions
pathexpr :: Parser Syntax
pathexpr =
  first >>= rest
  where
    next x =
      (Extend x <$> readsMy)
        <|> (Get . At x <$> readsMy)
    
    
    rest x =
      (next x >>= rest)
        <|> return x
    
    
    first =
      string                      -- '"' ...
        <|> parens disambigTuple  -- '(' ...
        <|> number                -- digit ...
        <|> (Block <$> readsMy)   -- '{' ...
        <|> (Var <$> readsMy)     -- '.' alpha ...
                                  -- alpha ...
        <?> "value"
        
        
    disambigTuple :: Parser Syntax
    disambigTuple = (readsMy >>= \ e -> case tryStmt e of 
      Nothing -> return e
      Just (Left p) ->
        (Block . Tup <$> liftA2 (:) (Set p <$> (stmtEq >> readsMy)) tuple1)
          <|> (Block . Tup . (Pun (Pub <$> p):) <$> tuple1)
          <|> return e
      Just (Right p) ->
        (Block . Tup . (Pun (Priv <$> p):) <$> tuple1)
          <|> return e)
        <|> (return . Block) (Tup [])
      where
        tryStmt (Var x) = case x of
          Pub t -> Just (Left (Pure t))
          Priv l -> Just (Right (Pure l))
        tryStmt (Get (e `At` x)) = (bimap wrap wrap) <$> tryStmt e where
          wrap :: Path Tag a -> Path Tag a
          wrap p = Free (p `At` x)
        tryStmt _ = Nothing
          

-- | Parse a block expression
instance (ReadMy a) => ReadMy (Block Tag a) where
  readsMy = block <|> (Tup <$> tuple)
  
  
instance (ShowMy k, ShowMy a) => ShowMy (Block k a) where
  showsMy b = case b of
    Tup []    -> showString "()"
    Tup [x]     -> showString "( " . showsMy x . showString ",)"
    Tup (x:xs)  -> showString "( " . showsMy x . flip (foldr (showSep ", ")) xs . showString " )"
    Rec []      -> showString "{}"
    Rec (y:ys)  -> showString "{ " . showsMy y . flip (foldr (showSep "; ")) ys . showString " }"
      
        
-- | Parse statement equals definition
stmtEq :: Parser ()
stmtEq = P.char '=' >> spaces
            
    
-- | Parse statement separators
semicolonsep :: Parser ()
semicolonsep =
  P.char ';' >> spaces
  
  
commasep :: Parser ()
commasep =
  P.char ',' >> spaces
  
  
ellipsissep :: Parser ()
ellipsissep =
  try (P.string "..." <* P.notFollowedBy (P.char '.')) >> spaces

  
-- | Parse different bracket types
braces :: Parser a -> Parser a
braces =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)

    
parens :: Parser a -> Parser a
parens =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    

staples :: Parser a -> Parser a
staples =
  P.between
    (P.char '[' >> spaces)
    (P.char ']' >> spaces)
    
        
-- | Parse either an expression wrapped in parens or a tuple form block
tuple :: ReadMy a => Parser [a]
tuple = parens (some <|> return [])
  where
    some = liftA2 (:) readsMy tuple1
    
    
tuple1 :: ReadMy a => Parser [a]
tuple1 = commasep >> P.sepEndBy readsMy commasep

        
block :: (ReadMy a) => Parser (Block Tag a)
block = Rec <$> braces (P.sepEndBy readsMy semicolonsep)
          
          
-- | Parse binary operators
readOr, readAnd, readEq, readNe, readLt, readGt, readLe, readGe, readAdd,
  readSub, readProd, readDiv, readPow  :: Parser Binop
readOr = P.char '|' >> spaces >> return Or
readAnd = P.char '&' >> spaces >> return And
readEq = P.char '=' >> spaces >> return Eq
readNe = try (P.string "!=") >> spaces >> return Ne
readLt = P.char '<' >> spaces >> return Lt
readGt = P.char '>' >> spaces >> return Gt
readLe = try (P.string "<=") >> spaces >> return Le
readGe = try (P.string ">=") >> spaces >> return Ge
readAdd = P.char '+' >> spaces >> return Add
readSub = P.char '-' >> spaces >> return Sub
readProd = P.char '*' >> spaces >> return Prod
readDiv = P.char '/' >> spaces >> return Div
readPow = P.char '^' >> spaces >> return Pow


instance ReadMy Binop where
  readsMy = P.choice   
    [ readOr
    , readAnd
    , readLt <|> readGt <|> readEq <|> readNe <|> readLe <|> readGe
    , readSub <|> readAdd
    , readDiv <|> readProd
    , readPow
    ]
  
showBinop :: Binop -> ShowS
showBinop Add   = showChar '+'
showBinop Sub   = showChar '-'
showBinop Prod  = showChar '*'
showBinop Div   = showChar '/'
showBinop Pow   = showChar '^'
showBinop And   = showChar '&'
showBinop Or    = showChar '|'
showBinop Lt    = showChar '<'
showBinop Gt    = showChar '>'
showBinop Eq    = showString "=="
showBinop Ne    = showString "!="  
showBinop Le    = showString "<="
showBinop Ge    = showString ">="
          

instance ShowMy Binop where
  showsMy = showBinop
  
  
-- | Parse unary operators
readNeg, readNot :: Parser Unop
readNeg = P.char '-' >> spaces >> return Neg
readNot = P.char '!' >> spaces >> return Not


instance ReadMy Unop where
  readsMy = readNeg <|> readNot


showUnop :: Unop -> ShowS
showUnop Neg = showChar '-'
showUnop Not = showChar '!'


instance ShowMy Unop where
  showsMy = showUnop


-- | Parse a statement of a block expression
instance (ReadMy a) => ReadMy (RecStmt Tag a) where
  readsMy = 
    declsym                 -- '\'' alpha
      <|> setrecstmt        -- '.' alpha ...
                            -- alpha ...
      <|> destructurestmt   -- '(' ...
    
  
instance (ShowMy k, ShowMy a) => ShowMy (RecStmt k a) where
  showsMy (DeclSym s) = showsMy s
  showsMy (DeclVar l) = showsMy l
  showsMy (l `SetRec` r) = showsMy l . showString " = " . showsMy r
    
    
instance (ReadMy k, ReadMy a) => ReadMy (Stmt k a) where
  readsMy = do
    x <- readsMy
    case x of
      Priv _ -> Pun <$> (path x) -- alpha ...
      Pub t -> do                   -- '.' alpha ...
        p <- path t
        (Set p <$> (stmtEq >> readsMy))
          <|> (return . Pun) (Pub <$> p)
      
  
instance (ShowMy k, ShowMy a) => ShowMy (Stmt k a) where 
  showsMy (Pun l) = showsMy l
  showsMy (l `Set` a) = showsMy l . showString " = " . showsMy a
  

-- | Parse a symbol declaration
declsym :: Parser (RecStmt k a)
declsym = DeclSym <$> readsMy


-- | Parse a recursive block set statement
setrecstmt :: ReadMy a => Parser (RecStmt Tag a)
setrecstmt =
  do
    v <- readsMy
    case v of
      Pub (Ident l) -> do                 -- '.' alpha ...
        p <- path l
        (next . SetPath) (Pub . Ident <$> p)
          <|> return (DeclVar p)
          
      _ -> path v >>= next . SetPath
  where
    next x = liftA2 SetRec (decomp1 x) (stmtEq >> readsMy)

        

-- | Parse a destructuring statement
destructurestmt :: (ReadMy k, ReadMy a) => Parser (RecStmt k a)
destructurestmt =
  do
    l <- decomp
    SetRec l <$> (stmtEq >> readsMy)
    
                    
                    
-- | Parse a valid lhs pattern for an assignment
instance ReadMy k => ReadMy (SetExpr k) where
  readsMy = 
    ((SetPath <$> readsMy) >>= decomp1)
      <|> decomp
    
    
instance ShowMy k => ShowMy (SetExpr k) where
  showsMy e = case e of
    SetPath x       -> showsMy x
    Decomp xs       -> showDecomp xs
    SetDecomp l xs  -> showsMy l . showChar ' ' . showDecomp xs
    where
      showDecomp [] = showString "()"
      showDecomp [x] = showString "( " . showsMy x . showString ",)"
      showDecomp (x:xs) = showString "( " . showsMy x . flip (foldr (showSep ", ")) xs
        . showString " )"
        
      
decomp :: ReadMy k => Parser (SetExpr k)
decomp = Decomp <$> parens tuple >>= decomp1
    
    
decomp1 :: ReadMy k => SetExpr k -> Parser (SetExpr k)
decomp1 x =
  ((SetDecomp x <$> parens tuple) >>= decomp1)
    <|> return x
    
    
-- | Parse a top-level sequence of statements
program :: Parser (NonEmpty (RecStmt Tag Syntax))
program =
  (do
    x <- readsMy
    (do
      semicolonsep
      xs <- P.sepEndBy readsMy semicolonsep
      return (x:|xs))
      <|> return (pure x))
    <* P.eof
    

showProgram :: NonEmpty (RecStmt Tag Syntax) -> ShowS
showProgram (x:|xs) = showsMy x  . flip (foldr (showSep ";\n\n")) xs

