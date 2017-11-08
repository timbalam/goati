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
  
  
type Tag = T.Text
  
  
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
  P.char '|' >> spaces
    
    
-- | Parse a set statement
setStmt :: Parser (Stmt Tag)
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
destructureStmt :: Parser (Stmt Tag)
destructureStmt =
  do
    x <- destructure
    P.char '='
    spaces
    y <- rhs
    return (x `Set` y)
    
    
-- | Parse any statement
stmt :: Parser (Stmt Tag)
stmt =
  setStmt                 -- '.' alpha ...
                          -- alpha ...
    <|> destructureStmt   -- '{' ...
    <?> "statement"

      
-- | Parse an addressable lhs pattern
path :: Parser (Path Tag)
path =
  first >>= rest
    where
      first =
        (field >>= return . Free . SelfAt)    -- '.'
          <|> (ident >>= return . Pure)       -- alpha
      
      
      next x =
        field >>= return . Free . At x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
          
    
-- | Parse a destructuring lhs pattern
destructure :: Parser (SetExpr (Path Tag) (PathPattern Tag))
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
matchStmt :: Parser (MatchStmt (Path Tag) (PathPattern Tag))
matchStmt =  
  (do
    x <- pathPattern                        -- '.' alpha
    (do
      P.char '='
      spaces
      y <- path
      return (x `Match` y))
      <|> (return . MatchPun . toPath) x)
    <|> (path >>= return . MatchPun)        -- alpha
  where
    toPath :: PathPattern Tag -> Path Tag
    toPath = Free . fmap toPath . outF
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser (SetExpr (Path Tag) (PathPattern Tag))
lhs =
  (path >>= return . SetPath)
    <|> destructure
    <?> "lhs"
  
  
-- | Parse a selection
pathPattern :: Parser (PathPattern Tag)
pathPattern =
  first >>= rest
    where
      first =
        field >>= return . InF . SelfAt
  

      next x =
        field >>= return . InF . At x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
    
    
-- | Parse an expression with binary operations
rhs :: Parser (Expr Tag)
rhs =
  orExpr        -- '!' ...
                -- '-' ...
                -- '"' ...
                -- '(' ...
                -- digit ...
                -- '{' ...
                -- '.' ...
                -- alpha ...

    
bracket :: Parser (Expr Tag)
bracket =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    rhs

  
pathExpr :: Parser (Expr Tag)
pathExpr =
  first >>= rest
    where
      next x =
        (bracket >>= return . App x)
          <|> (field >>= return . GetPath . At (InF x))
      
      
      rest x =
        (next x >>= rest)
          <|> return x
      
      
      first =
        string                                                -- '"' ...
          <|> bracket                                         -- '(' ...
          <|> number                                          -- digit ...
          <|> block                                           -- '{' ...
          <|> (field >>= return . GetPath . SelfAt)   -- '.' ...
          <|> (ident >>= return . GetEnv)    -- alpha ...
          <?> "rvalue"
      

-- | Parse a curly-brace wrapped sequence of statements
block :: Parser (Expr Tag)
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
unop :: Parser (Expr Tag)
unop =
  do
    s <- op
    x <- pathExpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orExpr :: Parser (Expr Tag)
orExpr =
  P.chainl1 andExpr orOp
    where
      orOp =
        P.char '|' >> spaces >> return (Binop Or)

      
andExpr :: Parser (Expr Tag)
andExpr =
  P.chainl1 cmpExpr andOp
    where
      andOp =
        P.char '&' >> spaces >> return (Binop And)

        
cmpExpr :: Parser (Expr Tag)
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
   
   
addExpr :: Parser (Expr Tag)
addExpr =
  P.chainl1 mulExpr addOp
    where
      addOp =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulExpr :: Parser (Expr Tag)
mulExpr =
  P.chainl1 powExpr mulOp
    where
      mulOp =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powExpr :: Parser (Expr Tag)
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
program :: Parser (NonEmpty (Stmt Tag))
program =
  (do
    x <- stmt
    (do
      stmtBreak
      xs <- P.sepEndBy stmt stmtBreak
      return (x:|xs))
      <|> return (x:|[]))
    <* P.eof


