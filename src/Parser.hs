{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Parser
  ( decfloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , ident
  , field
  , vis
  , path
  , unop
  , stmt
  , matchstmt
  , lhs
  , rhs
  , pathexpr
  , program
  )
  where
  
import Types.Parser

import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec
  ( (<|>)
  , (<?>)
  , try
  )
import Text.Parsec.Text ( Parser )
import Numeric( readHex, readOct )
import Control.Applicative( liftA2 )
import Data.Foldable( foldl', concat, toList )
import Data.List.NonEmpty( NonEmpty(..), nonEmpty )
import Data.Semigroup( (<>) )
import Control.Monad.Free

  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
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
    
    
-- | Parser for valid binary number
binary :: Parser Syntax
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parser for valid octal number
octal :: Parser Syntax
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parser for valid hexidecimal number
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
    
    
-- | Parser that parses whitespace and comments
spaces = P.spaces >> P.optional (comment >> spaces)
    
    
-- | Parser for valid numeric value
number :: Parser Syntax
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number")
    <* spaces

    
-- | Parser that succeeds when consuming an escaped character.
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

          
-- | Parser that succeeds when consuming a double-quote wrapped string.
string :: Parser Syntax
string =
  StringLit . T.pack <$> stringfragment

  
stringfragment :: Parser String
stringfragment =
  P.between
    (P.char '"')
    (P.char '"' >> spaces)
    (P.many (P.noneOf "\"\\" <|> escapedchars))

          
-- | Parser that succeeds when consuming a valid identifier string.
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
  Symbol . T.pack <$> ident
    

  
-- | Parse a valid field accessor
field :: Parser (Tag Symbol)
field =
  do
    point
    spaces
    (Id <$> parens symbol)
      <|> (Label . T.pack <$> ident)
      
    
-- | Parse an addressable lhs pattern 
path :: Parser a -> Parser (Path Symbol a)
path first = first >>= rest . Pure
  where
    rest x =
      (field >>= path . Free . At x)
        <|> return x
        
        
vis :: Parser (Vis Symbol)
vis =
  (Pub <$> field)
    <|> (Priv <$> ident)
    
    
-- | Parse an statement break
stmtbreak :: Parser ()
stmtbreak =
  P.char ';' >> spaces
  
  
-- | Parsers for different bracket types
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
declsym :: Parser Stmt
declsym = DeclSym <$> symbol

    
-- | Parse a set statement
setstmt :: Parser Stmt
setstmt =
  do
    l <- path vis
    (do
      l' <- decomp (SetPath l)
      P.char '='
      spaces
      r <- rhs
      return (l' `Set` r))
      <|> return (SetPun l)
  where
    decomp s =
      (blockexpr matchstmt >>= decomp . SetDecomp s)
      <|> return s
        

-- | Parse a destructuring statement
destructurestmt :: Parser Stmt
destructurestmt =
  do
    l <- blockexpr matchstmt >>= decomp . SetBlock
    P.char '='
    spaces
    r <- rhs
    return (l `Set` r)
  where
    decomp s =
      (blockexpr matchstmt >>= decomp . SetDecomp s)
       <|> return s
    
    
-- | Parse a statement of a block expression
stmt :: Parser Stmt
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
    <|> (path vis >>= return . MatchPun)    -- alpha
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser SetExpr
lhs = 
  (path vis >>= decomp . SetPath)
    <|> (blockexpr matchstmt >>= decomp . SetBlock)
    <?> "lhs"
  where
    decomp s =
      (blockexpr matchstmt >>= decomp . SetDecomp s)
      <|> return s
    
    
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
        <|> (Var <$> vis)               -- '.' alpha ...
                                        -- alpha ...
                                        -- '#' '"' ...
        <?> "value"
    
    
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
program :: Parser (NonEmpty Stmt)
program =
  (do
    x <- stmt
    (do
      stmtbreak
      xs <- P.sepEndBy stmt stmtbreak
      return (x:|xs))
      <|> return (pure x))
    <* P.eof

