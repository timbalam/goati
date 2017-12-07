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
  , destructure
  , unop
  , stmt
  , matchstmt
  , lhs
  , rhs
  , pathexpr
  , program
  )
  where
  
import Types.Parser hiding ( vis )

import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec
  ( (<|>)
  , (<?>)
  , try
  )
import Text.Parsec.Text ( Parser )
import Numeric
  ( readHex
  , readOct
  )
import Data.Foldable( foldl' )
import Data.List.NonEmpty( NonEmpty(..) )
import Control.Monad.Free

  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
  
  
-- | Parse a single decimal point / field accessor (disambiguated from extension dots)
point = P.char '.' <* P.notFollowedBy (P.char '.')

  
-- | Parse a block extension separator
extendbreak =
  try (P.string "...") >> spaces
    
    
-- | Parser for valid decimal or floating point number
decfloat :: Parser (Expr a)
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
binary :: Parser (Expr a)
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parser for valid octal number
octal :: Parser (Expr a)
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parser for valid hexidecimal number
hexidecimal :: Parser (Expr a)
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
    
    
-- | Parser that parses whitespace
spaces =
  P.spaces
    
    
-- | Parser for valid numeric value
number :: Parser (Expr a)
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number")
    <* spaces

    
-- | Parser that succeeds when consuming an escaped character.
escapedChars =
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
string :: Parser (Expr a)
string =
  do
    x <- stringfragment
    (return . StringLit) (T.pack x)
    where
      stringfragment =
        P.between
          (P.char '"')
          (P.char '"' >> spaces)
          (P.many (P.noneOf "\"\\" <|> escapedChars))

          
-- | Parser that succeeds when consuming a valid identifier string.
ident :: Parser Tag
ident =
  do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    (return . T.pack) (x:xs)

  
-- | Parse a valid field accessor
field :: Parser Tag
field =
  do
    point
    spaces
    ident
    
    
-- | Parse an addressable lhs pattern 
vis :: Parser (Vis Tag)
vis =
  (Priv <$> ident)
    <|> (Pub <$> field)
    
    
path :: Parser a -> Parser (Path a)
path first =
  first >>= rest . Pure
    where
      next x =
        field >>= return . Free . At x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
    
      
-- | Parse an statement break
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
    
  
blockexpr :: Parser a -> Parser b -> Parser ([a], Maybe b)
blockexpr stmt ext = braces (stmtfirst <|> last)
  where
    next =
      stmtnext
        <|> last
        
    stmtfirst = do
      x <- stmt
      (xs, m) <- next
      return (x:xs, m)
      
    stmtnext = do
      stmtbreak
      (stmtfirst 
        <|> return ([], Nothing))
      
    last = do
      m <- P.optionMaybe (extendbreak >> ext)
      return ([], m)
        
    
-- | Parse a set statement
setstmt :: Parser (Stmt (Vis Tag))
setstmt =
  do
    l <- path vis
    (do
      P.char '='
      spaces
      (do
        r <- rhs
        return (SetPath l `Set` r))
        <|> return (Declare l))
      <|> return (SetPun l)
        

-- | Parse a destructuring statement
destructurestmt :: Parser (Stmt (Vis Tag))
destructurestmt =
  do
    l <- destructure
    P.char '='
    spaces
    r <- rhs
    return (l `Set` r)
    
    
-- | Parse a statement of a block expression
stmt :: Parser (Stmt (Vis Tag))
stmt =
  setstmt                 -- '.' alpha ...
                          -- alpha ...
    <|> destructurestmt   -- '{' ...
    <?> "statement"
          
    
-- | Parse a destructuring lhs pattern
destructure :: Parser (SetExpr (Vis Tag))
destructure =
  (uncurry SetBlock <$> blockexpr matchstmt (path vis))
        
        
-- | Parse a match stmt
matchstmt :: Parser (MatchStmt (Vis Tag))
matchstmt =  
  (do
    r <- path field                        -- '.' alpha
    (do
      P.char '='
      spaces
      l <- lhs
      return (r `Match` l))
      <|> (return . MatchPun) (Pub <$> r))
    <|> (path vis >>= return . MatchPun)        -- alpha
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser (SetExpr (Vis Tag))
lhs =
    (SetPath <$> path vis)
      <|> destructure
      <?> "lhs"
    
    
-- | Parse an expression with binary operations
rhs :: Parser (Expr (Vis Tag))
rhs =
    orexpr    -- '!' ...
              -- '-' ...
              -- '"' ...
              -- '(' ...
              -- digit ...
              -- '{' ...
              -- '.' alpha ...
              -- alpha ...

  
pathexpr :: Parser (Expr (Vis Tag))
pathexpr =
  first >>= rest
  where
    next x =
      (parens rhs >>= return . Update x)
        <|> (field >>= return . Get . At x)
    
    
    rest x =
      (next x >>= rest)
        <|> return x
    
    
    first =
      string                                          -- '"' ...
        <|> parens rhs                                -- '(' ...
        <|> number                                    -- digit ...
        <|> (uncurry Block <$> blockexpr stmt rhs)    -- '{' ...
        <|> (Var <$> vis)                             -- '.' alpha ...
                                                      -- alpha ...
        <?> "value"
    
    
-- | Parse an unary operation
unop :: Parser (Expr (Vis Tag))
unop =
  do
    s <- op
    x <- pathexpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orexpr :: Parser (Expr (Vis Tag))
orexpr =
  P.chainl1 andexpr op
    where
      op =
        P.char '|' >> spaces >> return (Binop Or)

      
andexpr :: Parser (Expr (Vis Tag))
andexpr =
  P.chainl1 cmpexpr op
    where
      op =
        P.char '&' >> spaces >> return (Binop And)

        
cmpexpr :: Parser (Expr (Vis Tag))
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
   
   
addexpr :: Parser (Expr (Vis Tag))
addexpr =
  P.chainl1 mulexpr op
    where
      op =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulexpr :: Parser (Expr (Vis Tag))
mulexpr =
  P.chainl1 powexpr op
    where
      op =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powexpr :: Parser (Expr (Vis Tag))
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
program :: Parser (NonEmpty (Stmt (Vis Tag)))
program =
  (do
    x <- stmt
    (do
      stmtbreak
      xs <- P.sepEndBy stmt stmtbreak
      return (x:|xs))
      <|> return (pure x))
    <* P.eof

