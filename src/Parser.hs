{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts #-}
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
extendbreak :: Parser ()
extendbreak =
  try (P.string "..." <* P.notFollowedBy (P.char '.')) >> spaces
    
    
-- | Parser for valid decimal or floating point number
decfloat :: Parser Syntax_
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
binary :: Parser Syntax_
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: Parser Syntax_
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: Parser Syntax_
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
number :: Parser Syntax_
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
string :: Parser Syntax_
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
path :: Parser a -> Parser (Path a)
path first = first >>= rest . Pure
  where
    rest x =
      (field >>= rest . Free . At x)
        <|> return x
        
        
var :: Parser Var
var =
  (Pub <$> field)
    <|> (Priv . T.pack <$> ident)
    
    
-- | Parse an statement break
stmtbreak :: Parser ()
stmtbreak =
  P.char ';' >> spaces
  
  
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
    
  
blockexpr :: Parser a -> Parser [a]
blockexpr stmt = braces (P.sepEndBy stmt stmtbreak) 


-- | Parse a symbol declaration
declsym :: Parser Stmt_
declsym = flip DeclSym () <$> symbol

    
-- | Parse a set statement
setstmt :: Parser Stmt_
setstmt =
  do
    l <- path var
    (do
      P.char '='
      spaces
      r <- rhs
      return (SetPath l `Set` r))
      <|> return (SetPun l)
        

-- | Parse a destructuring statement
destructurestmt :: Parser Stmt_
destructurestmt =
  do
    l <- decomp
    P.char '='
    spaces
    r <- rhs
    return (l `Set` r)
    
    
decomp :: Parser SetExpr
decomp = braces (matchfirst <|> extendfirst) where
  
  matchfirst = do
    x <- matchstmt
    (do
      stmtbreak
      matchnext x)
      <|> extendnext [x]
      <|> return (SetBlock [x])
      
  matchnext x = ((\ e -> case e of
    SetBlock xs -> SetBlock (x:xs)
    SetDecomp l xs -> SetDecomp l (x:xs))
      <$> matchfirst)
    <|> return (SetBlock [x])
    
      
  extendfirst = extendnext []
  
  extendnext xs = do
    extendbreak
    l <- path var
    return (SetDecomp (SetPath l) xs)
    
    
-- | Parse a statement of a block expression
stmt :: Parser Stmt_
stmt =
  declsym                 -- '\'' alpha
    <|> setstmt           -- '.' alpha ...
                          -- alpha ...
    <|> destructurestmt   -- '{' ...
    <?> "statement"
        
        
-- | Parse a match stmt
matchstmt :: Parser MatchStmt
matchstmt =
  (do
    r <- path field                         -- '.' alpha
    (do
      P.char '='
      spaces
      l <- lhs
      return (r `Match` l))
      <|> (return . MatchPun) (Pub <$> r))
    <|> (path var >>= return . MatchPun)    -- alpha
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser SetExpr
lhs = 
  (path var >>= decomp . SetPath)
    <|> (blockexpr matchstmt >>= decomp . SetBlock)
    <?> "lhs"
  where
    decomp s =
      (blockexpr matchstmt >>= decomp . SetDecomp s)
      <|> return s
    
    
-- | Parse an expression with binary operations
rhs :: Parser Syntax_
rhs =
    orexpr    -- '!' ...
              -- '-' ...
              -- '"' ...
              -- '(' ...
              -- digit ...
              -- '{' ...
              -- '.' alpha ...
              -- alpha ...

  
pathexpr :: Parser Syntax_
pathexpr =
  first >>= rest
  where
    next x =
      (Extend x <$> blockexpr stmt)
        <|> (Get . At x <$> field)
    
    
    rest x =
      (next x >>= rest)
        <|> return x
    
    
    first =
      string                            -- '"' ...
        <|> parens rhs                  -- '(' ...
        <|> number                      -- digit ...
        <|> (Block <$> blockexpr stmt)  -- '{' ...
        <|> (Var <$> var)               -- '.' alpha ...
                                        -- alpha ...
                                        -- '#' '"' ...
        <?> "value"
    
    
-- | Parse an unary operation
unop :: Parser Syntax_
unop =
  do
    s <- op
    x <- pathexpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orexpr :: Parser Syntax_
orexpr =
  P.chainl1 andexpr op
    where
      op =
        P.char '|' >> spaces >> return (Binop Or)

      
andexpr :: Parser Syntax_
andexpr =
  P.chainl1 cmpexpr op
    where
      op =
        P.char '&' >> spaces >> return (Binop And)

        
cmpexpr :: Parser Syntax_
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
   
   
addexpr :: Parser Syntax_
addexpr =
  P.chainl1 mulexpr op
    where
      op =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulexpr :: Parser Syntax_
mulexpr =
  P.chainl1 powexpr op
    where
      op =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powexpr :: Parser Syntax_
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
program :: Parser (NonEmpty Stmt_)
program =
  (do
    x <- stmt
    (do
      stmtbreak
      xs <- P.sepEndBy stmt stmtbreak
      return (x:|xs))
      <|> return (pure x))
    <* P.eof

