{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes, LiberalTypeSynonyms #-}
module Parser
  ( decfloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , ident
  , field
  , var
  , path
  , unop
  , stmt
  , matchstmt
  , lhs
  , rhs
  , pathexpr
  , program
  , Parser, parse
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
import Data.Foldable( foldl', concat, toList )
import Data.List.NonEmpty( NonEmpty(..), nonEmpty )
import Data.Semigroup( (<>) )
import Data.Function( (&) )
--import Control.Monad.Free
import Control.Monad.State

  
-- | Parse a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
  
  
-- | Parse a single decimal point / field accessor (disambiguated from extension dots)
point :: Parser Char
point = try (P.char '.' <* P.notFollowedBy (P.char '.'))

  
-- | Parse a block extension separator
ellipsissep :: Parser ()
ellipsissep =
  try (P.string "..." <* P.notFollowedBy (P.char '.')) >> spaces
    
    
-- | Parser for valid decimal or floating point number
decfloat :: Parser Syntax
decfloat =
  prefixed
    <|> unprefixed
    <?> "decimal"
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
    
    
-- | Parse a valid binary number
binary :: Parser Syntax
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: Parser Syntax
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: Parser Syntax
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
      
      
      
-- | Parse a comment
comment :: Parser T.Text
comment = do
  try (P.string "//")
  s <- P.manyTill P.anyChar (try ((P.endOfLine >> return ()) <|> P.eof))
  return (T.pack s)
    
    
-- | Parse whitespace and comments
spaces :: Parser ()
spaces = P.spaces >> P.optional (comment >> spaces)
    
    
-- | Parse any valid numeric value
number :: Parser Syntax
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number")
    <* spaces

    
-- | Parse an escaped character.
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

          
-- | Parse a double-quote wrapped string.
string :: Parser Syntax
string =
  StringLit . T.pack <$> stringfragment

  
stringfragment :: Parser String
stringfragment =
  P.between
    (P.char '"')
    (P.char '"' >> spaces)
    (P.many (P.noneOf "\"\\" <|> escapedchars))

          
-- | Parse a valid identifier string.
ident :: Parser String
ident =
  do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    return (x:xs)
    

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
symbol :: Parser Symbol
symbol = do
  P.char '\''
  S_ . T.pack <$> ident
    

  
-- | Parse a valid field accessor
field :: Parser Tag
field =
  do
    point
    spaces
    (Symbol <$> parens symbol)
      <|> (Label . T.pack <$> ident)
      
    
-- | Parse an addressable lhs pattern 
path :: a -> Parser (Path a)
path = rest . Pure
  where
    rest x =
      (field >>= rest . Free . At x)
        <|> return x
        
        
var :: Parser Var
var =
  (Pub <$> field)
    <|> (Priv . T.pack <$> ident)
    
    
    
varpath :: Parser VarPath
varpath = var >>= path
    
    
-- | Parse a (recursive) statement break
semicolonsep :: Parser ()
semicolonsep =
  P.char ';' >> spaces
  
  
commasep :: Parser ()
commasep =
  P.char ',' >> spaces
  
  
-- | Parse different bracket types
braces :: Parser a -> Parser a
braces =
  P.between
    (try (P.char '{' <* P.notFollowedBy (P.char '#')) >> spaces)
    (P.char '}' >> spaces)
    
    
bracehashes :: Parser a -> Parser a
bracehashes =
  P.between
    (try (P.string "{#") >> spaces)
    (try (P.string "#}") >> spaces)

    
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
    
  
blockexpr :: Parser a -> Parser [a]
blockexpr stmt = braces (P.sepEndBy stmt semicolonsep) 


eqstmt :: Parser a -> Parser a
eqstmt lhs = do
  P.char '='
  spaces
  lhs


-- | Parse a symbol declaration
declsym :: Parser RecStmt
declsym = DeclSym <$> symbol


-- | Parse a recursive block set statement
setrecstmt :: Parser RecStmt
setrecstmt =
  do
    v <- var
    case v of
      Pub (Label l) -> do                 -- '.' alpha ...
        p <- path l
        (equalsnext . SetPath) (Pub . Label <$> p)
          <|> return (DeclVar p)
          
      _ -> path v >>= equalsnext . SetPath l
  where
    equalsnext x = SetRec x <$> eqstmt rhs

    
-- | Parse a set statement
setstmt :: Parser Stmt
setstmt =
  do
    x <- var
    case x of
      Priv _ -> SetPun <$> (path x)
      Pub t -> do
        p <- path t
        (Set p <$> eqstmt rhs)
          <|> (return . SetPun) (Pub <$> p)
        

-- | Parse a destructuring statement
destructurestmt :: Parser RecStmt
destructurestmt =
  do
    l <- decomp
    SetRec l <$> eqstmt rhs
    
    
decomp :: Parser SetExpr
decomp = parens (matchnext id <|> packnext id) where

  matchnext f = do
    x <- matchstmt
    (do
      commasep
      matchonlynext (f . (x:)))
      <|> packnext (f . (x:))
      <|> return (SetBlock (f [x]) Nothing)
      
  matchonlynext f =
    matchnext f
      <|> return (SetBlock (f []) Nothing)
  
  packnext f = do
    ellipsissep
    l <- varpath
    (return . SetBlock (f []) . Just) (SetPath l)
    
    
-- | Parse a statement of a block expression
recstmt :: Parser RecStmt
recstmt =
  declsym                   -- '\'' alpha
    <|> setrecstmt          -- '.' alpha ...
                            -- alpha ...
    <|> destructurestmt  -- '(' ...
    <?> "statement"
    
    
stmt :: Parser Stmt
stmt = 
  setstmt                 -- '.' alpha ...
                          -- alpha ...
    <?> "statement"
        
        
-- | Parse a match stmt
matchstmt :: Parser MatchStmt
matchstmt =
  do
    x <- var
    case x of
      Priv _ -> MatchPun <$> path x   -- alpha
      Pub t -> do                     -- '.' alpha
        p <- path t
        (Match p <$> eqstmt lhs)
          <|> (return . MatchPun) (Pub <$> p)
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser SetExpr
lhs = 
  (SetPath <$> varpath)
    <|> decomp
    <?> "lhs"
    
    
-- | Parse an expression with binary operations
rhs :: Parser Syntax
rhs =
    orexpr    -- '!' ...
              -- '-' ...
              -- '"' ...
              -- '(' ...
              -- digit ...
              -- '{' ...
              -- '.' alpha ...
              -- alpha ...

  
pathexpr :: Parser Syntax
pathexpr =
  first >>= rest
  where
    next x =
      (Extend x <$> (block <|> tuple))
        <|> (Get . At x <$> field)
    
    
    rest x =
      (next x >>= rest)
        <|> return x
    
    
    first =
      string                          -- '"' ...
        <|> parens disambiRhsTuple    -- '(' ...
        <|> number                    -- digit ...
        <|> Block <$> block           -- '{' ...
        <|> (Var <$> var)             -- '.' alpha ...
                                      -- alpha ...
                                      -- '#' '"' ...
        <?> "value"
        
    disambigRhsTuple = (Tup [] . Just <$> (ellipsissep >> rhs))
        <|> (try notRhs >>= tupleNotRhs)
        <|> rhs
        <|> (return . Block) (Tup [] Nothing)
        
        
        
-- | Minimum parsing required to disambiguate a tuple from a rhs value
data NotRhs =
    StmtEq (Path Tag)
  | PunComma (Path Var)
  | PunEllipsis (Path Var)
  
  
notRhs :: Parser NotRhs
notRhs = do
  x <- var
  case var of
    Priv _ -> path x >>= endpun
    Pub t -> do
      l <- path t
      (do 
        P.char '='
        spaces
        return (StmtEq l))
        <|> endpun (Pub <$> l)
  where
    endpun p =
      (commasep >> return (PunComma p))
        <|> (ellipsissep >> return (PunEllipsis p))
        
        
        
tupleNotRhs :: NotRhs -> Parser Block   
tupleNotRhs s = case s of 
  StmtEq p -> Set p <$> rhs >>= trailnext . (:)
  
  PunComma p -> stmtonlynext (SetPun p:)
  
  PunEllipsis p -> pack (SetPun p:)
  where
    trailnext f = 
      (commasep >> stmtonlynext f)
        <|> (ellipsissep >> pack f)
  
    stmtonlynext f = (do
      x <- stmt
      (trailnext (f . (x:)))
        <|> return (Tup (f [x]) Nothing))
      <|> return (Tup (f []) Nothing)
      
    pack f = Tup (f []) . Just <$> rhs
        
        
-- | Parse either an expression wrapped in parens or a tuple form block
tuple :: Parser Block
tuple = parens (stmtfirst <|> packfirst)
  where
    stmtfirst = stmt >>= rest . (:)
    packfirst = packnext id
    
    rest f =
      (commasep >> stmtonlynext f) <|> packnext f

    stmtnext f = do
      x <- stmt
      (rest (f . (x:)))
        <|> return (Tup (f [x]) Nothing)
        
    stmtonlynext f = 
      stmtnext f <|> return (Tup (f []) Nothing)
      
    packnext f = Tup (f []) . Just <$> (ellipsissep >> rhs)

        
block :: Parser Block
block = Rec <$> P.sepEndBy recstmt semicolonsep
    
    
-- | Parse an unary operation
unop :: Parser Syntax
unop =
  do
    s <- op
    x <- pathexpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orexpr :: Parser Syntax
orexpr =
  P.chainl1 andexpr op
    where
      op =
        P.char '|' >> spaces >> return (Binop Or)

      
andexpr :: Parser Syntax
andexpr =
  P.chainl1 cmpexpr op
    where
      op =
        P.char '&' >> spaces >> return (Binop And)

        
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
    op =
      try (P.string "==" >> spaces >> return (Binop Eq))
        <|> try (P.string "!=" >> spaces >> return (Binop Ne))
        <|> try (P.string ">=" >> spaces >> return (Binop Ge))
        <|> try (P.string "<=" >> spaces >> return (Binop Le))
        <|> (P.char '>' >> spaces >> return (Binop Gt))
        <|> (P.char '<' >> spaces >> return (Binop Lt))
   
   
addexpr :: Parser Syntax
addexpr =
  P.chainl1 mulexpr op
    where
      op =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulexpr :: Parser Syntax
mulexpr =
  P.chainl1 powexpr op
    where
      op =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powexpr :: Parser Syntax
powexpr =
  P.chainl1 term op
    where
      op =
        P.char '^' >> spaces >> return (Binop Pow)
      
      term =
        unop            -- '!'
                        -- '-'
          <|> pathexpr  -- '"'
                        -- '('
                        -- digit
                        -- '{'
                        -- '.'
                        -- alpha
    
    
-- | Parse a top-level sequence of statements
program :: Parser (NonEmpty RecStmt)
program =
  (do
    x <- recstmt
    (do
      semicolonsep
      xs <- P.sepEndBy recstmt semicolonsep
      return (x:|xs))
      <|> return (pure x))
    <* P.eof

