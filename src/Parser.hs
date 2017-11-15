{-# LANGUAGE DeriveFunctor #-}
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
  
  
data Vis a = Pub a | Priv a
  deriving (Eq, Functor)
  

instance Applicative Vis where
  pure = Pub
  
  
  Pub f <*> Pub a = Pub (f a)
  Pub f <*> Priv a = Priv (f a)
  Priv f <*> Pub a = Priv (f a)
  Priv f <*> Priv a = Priv (f a)
  
  
  
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
    return (StringLit (T.pack x))
    where
      stringFragment =
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
    return (T.pack (x:xs))

-- | Parse a valid field accessor
field :: Parser Tag
field =
  do
    P.char '.'
    spaces
    ident 
    
      
-- | Parse an statement break
stmtBreak =
  P.char ';' >> spaces
  
  
-- | Parse a node concatenation separator
sepConcat =
  try (P.string "... ") >> spaces
    
    
-- | Parse a set statement
setStmt :: Parser (Stmt (Vis Tag))
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
destructureStmt :: Parser (Stmt (Vis Tag))
destructureStmt =
  do
    x <- destructure
    P.char '='
    spaces
    y <- rhs
    return (x `Set` y)
    
    
-- | Parse any statement
stmt :: Parser (Stmt (Vis Tag))
stmt =
  setStmt                 -- '.' alpha ...
                          -- alpha ...
    <|> destructureStmt   -- '{' ...
    <?> "statement"

      
-- | Parse an addressable lhs pattern
path :: Parser (Path (Vis Tag))
path =
  first >>= rest
    where
      first =
        (field >>= return . Pure . Pub)           -- '.'
          <|> (ident >>= return . Pure . Priv)    -- alpha
      
      
      next x =
        field >>= return . Free . At x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
          
    
-- | Parse a destructuring lhs pattern
destructure :: Parser (SetExpr (Path (Vis Tag)) (Path Tag))
destructure =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    blockExpr
  where
    blockExpr = 
      stmtFirst           -- '{' ...
                          -- '.' alpha ...
                          -- alpha ..
        <|> concatNext    -- '|' ...
  
    stmtFirst =
      do
        x <- matchStmt
        SetBlock xs m <-
          stmtNext           -- ';' ...
            <|> concatNext   -- '|' ...
                             -- '}' ...
        return (SetBlock (x:xs) m)
         
         
    stmtNext =
      do
        stmtBreak
        stmtFirst                           -- '{' ...
                                            -- '.' alpha ...
                                            -- alpha ...
          <|> return (SetBlock [] Nothing)  -- '}' ...
          
          
    concatNext =
      do
        m <- P.optionMaybe (sepConcat >> path)
        return (SetBlock [] m)
        
        
-- | Parse a match stmt
matchStmt :: Parser (MatchStmt (Path (Vis Tag)) (Path Tag))
matchStmt =  
  (do
    x <- pathPattern                        -- '.' alpha
    (do
      P.char '='
      spaces
      y <- lhs
      return (x `Match` y))
      <|> (return . MatchPun . fmap Pub) x)
    <|> (path >>= return . MatchPun)        -- alpha
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser (SetExpr (Path (Vis Tag)) (Path Tag))
lhs =
  (path >>= return . SetPath)
    <|> destructure
    <?> "lhs"
  
  
-- | Parse a selection
pathPattern :: Parser (Path Tag)
pathPattern =
  first >>= rest
    where
      first =
        field >>= return . Pure
  

      next x =
        field >>= return . Free . At x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
    
    
-- | Parse an expression with binary operations
rhs :: Parser (Expr (Vis Tag))
rhs =
  orExpr        -- '!' ...
                -- '-' ...
                -- '"' ...
                -- '(' ...
                -- digit ...
                -- '{' ...
                -- '.' ...
                -- alpha ...

    
bracket :: Parser (Expr (Vis Tag))
bracket =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    rhs

  
pathExpr :: Parser (Expr (Vis Tag))
pathExpr =
  first >>= rest
    where
      next x =
        (block >>= return . Update x)
          <|> (field >>= return . Get . At x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x
      
      
      first =
        string                                  -- '"' ...
          <|> bracket                           -- '(' ...
          <|> number                            -- digit ...
          <|> block                             -- '{' ...
          <|> (field >>= return . Var . Pub)    -- '.' ...
          <|> (ident >>= return . Var . Priv)   -- alpha ...
          <?> "value"
      

-- | Parse a curly-brace wrapped sequence of statements
block :: Parser (Expr (Vis Tag))
block =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    blockExpr
  where
    blockExpr =
      stmtFirst
        <|> concatNext
        
        
    stmtFirst =
      do
        x <- stmt
        Block xs ts <- stmtNext <|> concatNext
        return (Block (x:xs) ts)
        
        
    stmtNext =
      do
        stmtBreak
        stmtFirst
          <|> return (Block [] [])
          
    
    concatNext =
      do
        ts <- P.many (sepConcat >> rhs)
        return (Block [] ts)
    
    
-- | Parse an unary operation
unop :: Parser (Expr (Vis Tag))
unop =
  do
    s <- op
    x <- pathExpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orExpr :: Parser (Expr (Vis Tag))
orExpr =
  P.chainl1 andExpr orOp
    where
      orOp =
        P.char '|' >> spaces >> return (Binop Or)

      
andExpr :: Parser (Expr (Vis Tag))
andExpr =
  P.chainl1 cmpExpr andOp
    where
      andOp =
        P.char '&' >> spaces >> return (Binop And)

        
cmpExpr :: Parser (Expr (Vis Tag))
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
   
   
addExpr :: Parser (Expr (Vis Tag))
addExpr =
  P.chainl1 mulExpr addOp
    where
      addOp =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulExpr :: Parser (Expr (Vis Tag))
mulExpr =
  P.chainl1 powExpr mulOp
    where
      mulOp =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powExpr :: Parser (Expr (Vis Tag))
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
program :: Parser (NonEmpty (Stmt (Vis Tag)))
program =
  (do
    x <- stmt
    (do
      stmtBreak
      xs <- P.sepEndBy stmt stmtBreak
      return (x:|xs))
      <|> return (x:|[]))
    <* P.eof


