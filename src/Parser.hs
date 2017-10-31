module Parser
  ( decFloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , ident
  , field
  , pathPattern
  , lhs
  , path
  , destructure
  , rhs
  , unop
  , orExpr
  , pathExpr
  , block
  , program
  )
  where
  
import Types.Parser

import qualified Data.Text as T
import Data.String
  ( IsString(..)
  )
import qualified Text.Parsec as P hiding
  ( try )
import Text.Parsec
  ( (<|>)
  , (<?>)
  , try
  )
import Text.Parsec.Text
  ( Parser
  )
import Numeric
  ( readHex
  , readOct
  )
import Data.List( foldl' )
import Data.List.NonEmpty( NonEmpty(..), toList )
import Control.Monad.Free


class ReadMy a where
  readMy :: String -> Parser a
  
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  P.sepBy1 d (P.optional (P.char '_'))
    
    
-- | Parser for valid decimal or floating point number
decFloat :: Parser (ExprF a b)
decFloat =
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
        fracNext xs                             -- int frac
                                                -- int frac exp
          <|> expNext xs                        -- int exp
          <|> (return . IntegerLit . read) xs   -- int
          
    fracNext xs =
      do 
        y <- P.char '.'
        m <- P.optionMaybe (integer P.digit)
        case m of
          Nothing ->
            -- frac
            (return . NumberLit . read) (xs ++ [y, '0'])
            
          Just ys ->
            expNext (xs ++ [y] ++ ys)   -- frac exp
              <|>
                (return . NumberLit . read) (xs ++ [y] ++ ys)
                                      -- frac
          
    expNext xs =
      do 
        e <- P.oneOf "eE"
        sgn <- P.option [] (P.oneOf "+-" >>= return . (:[]))
        ys <- integer P.digit
        (return . NumberLit . read) (xs ++ e:sgn ++ ys)
    
    
-- | Parser for valid binary number
binary :: Parser (ExprF a b)
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parser for valid octal number
octal :: Parser (ExprF a b)
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parser for valid hexidecimal number
hexidecimal :: Parser (ExprF a b)
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
    
    
-- | Parser that parses whitespace
spaces =
  P.spaces
    
    
-- | Parser for valid numeric value
number :: Parser (ExprF a b)
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decFloat
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
string :: Parser (ExprF a b)
string =
  do
    x <- stringFragment
    xs <- P.many stringFragment
    return (StringLit (T.pack <$> (x :| xs)))
    where
      stringFragment =
        P.between
          (P.char '"')
          (P.char '"' >> spaces)
          (P.many (P.noneOf "\"\\" <|> escapedChars))

          
-- | Parser that succeeds when consuming a valid identifier string.
ident :: Parser T.Text
ident =
  do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    return (T.pack (x:xs))

-- | Parse a valid field accessor
field :: Parser T.Text
field =
  do
    P.char '.'
    spaces
    ident 
    
      
-- | Parse an statement break
stmtBreak =
  P.char ';' >> spaces
    
    
-- | Parse a set statement
setStmt :: Parser (Stmt Vis (Expr Vis))
setStmt =
  do
    x <- path
    (do
      P.char '='
      spaces
      (do
        y <- rhs
        return (SetPath x `Set` y))
        <|> return (Declare x))
      <|> return (SetPun x)
        

-- | Parse a destructuring statement
destructureStmt :: Parser (Stmt Vis (Free (ExprF Vis) Vis))
destructureStmt =
  do
    x <- destructure
    P.char '='
    spaces
    y <- rhs
    return (x `Set` y)
    
    
-- | Parse any statement
stmt :: Parser (Stmt Vis (Expr Vis))
stmt =
  setStmt                 -- '.' alpha ...
                          -- alpha ...
    <|> destructureStmt   -- '{' ...
    <?> "statement"

      
-- | Parse an addressable lhs pattern
path :: Parser (Path Vis)
path =
  first >>= rest
    where
      first =
        (field >>= return . At (Pure Priv))       -- '.'
          <|> (ident >>= return . At (Pure Pub))  -- alpha
      
      
      next x =
        field >>= return . At (Free x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x
          
    
-- | Parse a destructuring lhs pattern
destructure :: Parser (SetExpr Vis)
destructure =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (blockExpr
      matchStmt   -- '{' ...
                  -- '.' alpha ...
                  -- alpha ..
      path
      >>= return . SetBlock)
    
    
    
blockExpr :: Parser s -> Parser p -> Parser (BlockExpr s p)
blockExpr stmt pack =
  do
    xs <- P.sepEndBy stmt stmtBreak
    (do
      P.string "*"
      y <- pack
      return (y :& xs))
      <|> return (Closed xs)

            
-- | Parse an lval assignment
matchPath :: Parser (MatchStmt Vis)
matchPath = 
  (do
    x <- pathPattern                        -- '.' alpha
    (do
      P.char '='
      spaces
      y <- lhs
      return (SetPath x `Match` y))
      <|> (return . MatchPun) (const Pub <$> x))
    <|> (path >>= return . MatchPun)        -- alpha

    
    
-- | Parse a destructuring lval assignment
matchBlock :: Parser (MatchStmt Vis)
matchBlock =
  do
    x <- blockPattern
    P.char '='
    spaces
    y <- lhs
    return (x `Match` y)
        
        
-- | Parse a match stmt
matchStmt :: Parser (MatchStmt Vis)
matchStmt = 
  matchBlock       -- '{' ...
    <|> matchPath  -- '.' ...
                   -- alpha ...
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser (SetExpr Vis)
lhs =
  (path >>= return . SetPath)
    <|> destructure
    <?> "lhs"
  
  
-- | Parse a selection
pathPattern :: Parser PathPattern
pathPattern =
  first >>= rest
    where
      first =
        field >>= return . At (Pure ())
  

      next x =
        field >>= return . At (Free x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x
        
        
-- | Description
blockPattern :: Parser PatternExpr
blockPattern =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (blockExpr asStmt pathPattern >>= return . SetBlock)
        
        
-- | Parse a match to a path pattern
asPathStmt :: Parser AsStmt
asPathStmt =
  do
    x <- pathPattern
    (do
      P.char '='
      spaces
      y <- patternExpr
      return (SetPath x `Match` y))
      <|> return (MatchPun x)
      
   
-- | Parse a match to a block pattern
asBlockStmt :: Parser AsStmt
asBlockStmt =
  do
    x <- blockPattern
    P.char '='
    spaces
    y <- patternExpr
    return (x `Match` y)
        
        
-- | Parse an as statement
asStmt :: Parser AsStmt
asStmt =
  asPathStmt          -- '.'
                      -- alpha
    <|> asBlockStmt   -- '{'
        
          
-- | Parse a selection pattern
patternExpr :: Parser PatternExpr
patternExpr =
  (pathPattern >>= return . SetPath)    -- '.'
    <|> blockPattern                    -- '{'
    
    
-- | Parse an expression with binary operations
rhs :: Parser (Expr Vis)
rhs =
  orExpr        -- '!' ...
                -- '-' ...
                -- '"' ...
                -- '(' ...
                -- digit ...
                -- '{' ...
                -- '.' ...
                -- alpha ...

    
bracket :: Parser (Expr Vis)
bracket =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    rhs

  
pathExpr :: Parser (Expr Vis)
pathExpr =
  first >>= rest
    where
      next x =
        (bracket >>= return . Extend x)
          <|> (field >>= return . GetPath . At (Free x))
      
      
      rest x =
        (next x >>= rest)
          <|> return x
      
      
      first =
        string                                                -- '"' ...
          <|> bracket                                         -- '(' ...
          <|> number                                          -- digit ...
          <|> block                                           -- '{' ...
          <|> (field >>= return . GetPath . At (Pure Pub))   -- '.' ...
          <|> (ident >>= return . GetPath . At (Pure Priv))    -- alpha ...
          <?> "rvalue"
      

-- | Parse a curly-brace wrapped sequence of statements
block :: Parser (Expr Vis)
block =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (blockExpr stmt pathExpr >>= return . Block)
    
    
-- | Parse an unary operation
unop :: Parser (Expr Vis)
unop =
  do
    s <- op
    x <- pathExpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orExpr :: Parser (Expr Vis)
orExpr =
  P.chainl1 andExpr orOp
    where
      orOp =
        P.char '|' >> spaces >> return (Binop Or)

      
andExpr :: Parser (Expr Vis)
andExpr =
  P.chainl1 cmpExpr andOp
    where
      andOp =
        P.char '&' >> spaces >> return (Binop And)

        
cmpExpr :: Parser (Expr Vis)
cmpExpr = 
  do
    a <- addExpr
    (do
       s <- cmpOp
       b <- addExpr
       return (s a b))
      <|> return a
  where
    cmpOp =
      try (P.string "==" >> spaces >> return (Binop Eq))
        <|> try (P.string "!=" >> spaces >> return (Binop Ne))
        <|> try (P.string ">=" >> spaces >> return (Binop Ge))
        <|> try (P.string "<=" >> spaces >> return (Binop Le))
        <|> (P.char '>' >> spaces >> return (Binop Gt))
        <|> (P.char '<' >> spaces >> return (Binop Lt))
   
   
addExpr :: Parser (Expr Vis)
addExpr =
  P.chainl1 mulExpr addOp
    where
      addOp =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulExpr :: Parser (Expr Vis)
mulExpr =
  P.chainl1 powExpr mulOp
    where
      mulOp =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powExpr :: Parser (Expr Vis)
powExpr =
  P.chainl1 term powOp
    where
      powOp =
        P.char '^' >> spaces >> return (Binop Pow)
      
      
      term =
        unop            -- '!'
                        -- '-'
          <|> pathExpr  -- '"'
                        -- '('
                        -- digit
                        -- '{'
                        -- '.'
                        -- alpha
    
    
-- | Parse a top-level sequence of statements
program :: Parser (NonEmpty (Stmt Vis (Expr Vis)))
program =
  do
    x <- stmt
    stmtBreak
    xs <- P.sepEndBy stmt stmtBreak
    P.eof
    return (x:|xs)


