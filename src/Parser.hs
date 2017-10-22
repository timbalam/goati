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


class ReadMy a where
  readMy :: String -> Parser a
  
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  P.sepBy1 d (P.optional (P.char '_'))
    
    
-- | Parser for valid decimal or floating point number
decFloat :: Parser (Expr a)
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
string :: Parser (Expr a)
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
ident :: IsString a => Parser a
ident =
  do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    return (fromString (x:xs))

-- | Parse a valid field accessor
field :: IsString a => Parser a
field =
  do
    P.char '.'
    spaces
    ident 
    
      
-- | Parse an statement break
stmtBreak =
  P.char ';' >> spaces
    
    
-- | Parse a set statement
setStmt :: IsString a => Parser (Stmt a)
setStmt =
  do
    x <- path
    (do
      P.char '='
      spaces
      m <- P.optionMaybe rhs
      case m of
        Just y ->
          return (SetPath x `Set` y)
          
        Nothing ->
           return (Declare x))
      <|> return (SetPun x)
        

-- | Parse a destructuring statement
destructureStmt :: IsString a => Parser (Stmt a)
destructureStmt =
  do
    x <- destructure
    P.char '='
    spaces
    y <- rhs
    return (x `Set` y)
    
    
-- | Parse any statement
stmt :: IsString a => Parser (Stmt a)
stmt =
  setStmt                 -- '.' alpha ...
                          -- alpha ...
    <|> destructureStmt   -- '{' ...
    <?> "statement"

      
-- | Parse an addressable lhs pattern
path :: IsString a => Parser (Path a)
path =
  first >>= rest
    where
      first =
        (field >>= return . SelfAt)        -- '.'
          <|> (ident >>= return . EnvAt)  -- alpha
      
      
      next x =
        field >>= return . At x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
          
    
-- | Parse a destructuring lhs pattern
destructure :: IsString a => Parser (SetExpr a)
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
matchPath :: IsString a => Parser (MatchStmt a)
matchPath = 
  do                                   
    m <- P.optionMaybe pathPattern        -- '.' alpha
    case m of
      Just x ->
        (do
          P.char '='
          spaces
          y <- lhs
          return (AsPath x `Match` y))
          <|> return (MatchPun (toPath x))
          
      Nothing ->
        path >>= return . MatchPun        -- alpha
        
  where
    toPath :: PathPattern a -> Path a
    toPath (SelfAtP x) = SelfAt x
    toPath (s `AtP` x) = toPath s `At` x
    
    
-- | Parse a destructuring lval assignment
matchBlock :: IsString a => Parser (MatchStmt a)
matchBlock =
  do
    x <- blockPattern
    P.char '='
    spaces
    y <- lhs
    return (x `Match` y)
        
        
-- | Parse a match stmt
matchStmt :: IsString a => Parser (MatchStmt a)
matchStmt = 
  matchBlock       -- '{' ...
    <|> matchPath  -- '.' ...
                   -- alpha ...
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: IsString a => Parser (SetExpr a)
lhs =
  (path >>= return . SetPath)
    <|> destructure
    <?> "lhs"
  
  
-- | Parse a selection
pathPattern :: IsString a => Parser (PathPattern a)
pathPattern =
  first >>= rest
    where
      first =
        field >>= return . SelfAtP
  

      next x =
        field >>= return . AtP x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
        
        
-- | Description
blockPattern :: IsString a => Parser (PatternExpr a)
blockPattern =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (blockExpr asStmt pathPattern >>= return . AsBlock)
        
        
-- | Parse a match to a path pattern
asPathStmt :: IsString a => Parser (AsStmt a)
asPathStmt =
  do
    x <- pathPattern
    (do
      P.char '='
      spaces
      y <- patternExpr
      return (AsPath x `As` y))
      <|> return (AsPun x)
      
   
-- | Parse a match to a block pattern
asBlockStmt :: IsString a => Parser (AsStmt a)
asBlockStmt =
  do
    x <- blockPattern
    P.char '='
    spaces
    y <- patternExpr
    return (x `As` y)
        
        
-- | Parse an as statement
asStmt :: IsString a => Parser (AsStmt a)
asStmt =
  asPathStmt          -- '.'
                      -- alpha
    <|> asBlockStmt   -- '{'
        
          
-- | Parse a selection pattern
patternExpr :: IsString a => Parser (PatternExpr a)
patternExpr =
  (pathPattern >>= return . AsPath)   -- '.'
    <|> blockPattern                  -- '{'
    
    
-- | Parse an expression with binary operations
rhs :: IsString a => Parser (Expr a)
rhs =
  orExpr        -- '!' ...
                -- '-' ...
                -- '"' ...
                -- '(' ...
                -- digit ...
                -- '{' ...
                -- '.' ...
                -- alpha ...

    
bracket :: IsString a => Parser (Expr a)
bracket =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    rhs

  
pathExpr :: IsString a => Parser (Expr a)
pathExpr =
  first >>= rest
    where
      next x =
        (bracket >>= return . Extend x)
          <|> (field >>= return . Get x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x
      
      
      first =
        string                              -- '"' ...
          <|> bracket                       -- '(' ...
          <|> number                        -- digit ...
          <|> block                         -- '{' ...
          <|> (field >>= return . GetSelf)   -- '.' ...
          <|> (ident >>= return . GetEnv)   -- alpha ...
          <?> "rvalue"
      

-- | Parse a curly-brace wrapped sequence of statements
block :: IsString a => Parser (Expr a)
block =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (blockExpr stmt pathExpr >>= return . Block)
    
    
-- | Parse an unary operation
unop :: IsString a => Parser (Expr a)
unop =
  do
    s <- op
    x <- pathExpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orExpr :: IsString a => Parser (Expr a)
orExpr =
  P.chainl1 andExpr orOp
    where
      orOp =
        P.char '|' >> spaces >> return (Binop Or)

      
andExpr :: IsString a => Parser (Expr a)
andExpr =
  P.chainl1 cmpExpr andOp
    where
      andOp =
        P.char '&' >> spaces >> return (Binop And)

        
cmpExpr :: IsString a => Parser (Expr a)
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
   
   
addExpr :: IsString a => Parser (Expr a)
addExpr =
  P.chainl1 mulExpr addOp
    where
      addOp =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulExpr :: IsString a => Parser (Expr a)
mulExpr =
  P.chainl1 powExpr mulOp
    where
      mulOp =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powExpr :: IsString a => Parser (Expr a)
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
program :: IsString a => Parser (NonEmpty (Stmt a))
program =
  do
    x <- stmt
    stmtBreak
    xs <- P.sepEndBy stmt stmtBreak
    P.eof
    return (x:|xs)


