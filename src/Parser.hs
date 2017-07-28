module Parser
  ( float
  , decimal
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , fieldId
  , name
  , relativepath
  , pattern
  , laddress
  , destructure
  , rhs
  , unop
  , and_expr
  , raddress
  , structure
  , program
  ) where
  
import Types.Parser

import qualified Text.Parsec as P hiding
  ( try )
import Text.Parsec
  ( (<|>)
  , (<?>)
  , try
  )
import Text.Parsec.String
  ( Parser
  )
import Numeric
  ( readHex
  , readOct
  )
import Data.List( foldl' )
  
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  P.sepBy1 d (P.optional $ P.char '_')
    
    
-- | Parser for valid floating point number
float :: Parser Rval
float =
  do
    xs <- integer P.digit
    y <- P.char '.'
    ys <- P.option "0" (integer P.digit)
    (return . NumberLit . read) (xs ++ [y] ++ ys)
    
    
-- | Parser for valid decimal number
decimal :: Parser Rval
decimal =
  do
    P.optional (try (P.string "0d"))
    NumberLit . read <$> integer P.digit
    
    
-- | Parser for valid binary number
binary :: Parser Rval
binary =
  do
    try (P.string "0b")
    NumberLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parser for valid octal number
octal :: Parser Rval
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . NumberLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parser for valid hexidecimal number
hexidecimal :: Parser Rval
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . NumberLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
    
    
-- | Parser for valid numeric value
number :: Parser Rval
number =
  binary
    <|> octal
    <|> hexidecimal
    <|> try float
    <|> decimal
    <?> "number"

    
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
string :: Parser Rval
string =
  P.sepBy1 string_fragment spaces >>= return . StringLit . concat
    where
      string_fragment =
        P.between
          (P.char '"')
          (P.char '"')
          (P.many (P.noneOf "\"\\" <|> escapedChars))

          
-- | Parser that succeeds when consuming a valid identifier string.
fieldId :: Parser FieldId
fieldId =
  do
    x <- P.letter
    xs <- P.many P.alphaNum
    return (Field (x:xs))
    
    
-- | Parser that parses whitespace
spaces =
  P.spaces

-- | Modify a parser to trim whitespace
trim =
  P.between spaces spaces

-- | Parse a valid node name
name :: Parser FieldId
name =
  do
    P.char '.'
    spaces
    fieldId
    
    
pattern :: Parser Pattern
pattern =
  (Address <$> laddress) <|> destructure

  
-- | Parse a relative path
relativepath :: Parser Selection
relativepath =
  first >>= rest
    where
      first =
        name >>= return . SelectSelf
  

      next x =
        try (spaces >> name >>= return . Select x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x

      
laddress :: Parser Lval
laddress =
  first >>= rest
    where
      first =
        (name >>= return . InSelf)
          <|> (fieldId >>= return . InEnv)
      
      
      next x =
        try (spaces >> name >>= return . In x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x

      
-- | Parse an statement break
stmt_break =
   try (trim (P.char ';'))

as_stmt :: Parser Lstmt
as_stmt = 
  do
    x <- relativepath
    trim (P.char '=')
    y <- pattern
    return (x `As` y)
    
    
reversible_unpack_stmt :: Parser Lstmt
reversible_unpack_stmt =
  do
    P.char '*'
    x <- laddress
    return (RemainingAs x)
    
    
-- | Parse a destructuring statement
destructure :: Parser Pattern
destructure =
  P.between
    (P.char '{')
    (P.char '}')
    (trim destructure_body)
    >>= return . Destructure
  where
    destructure_body =
      unpack_first_body <|> assign_first_body
  
    
    unpack_first_body =
      do
        x <- reversible_unpack_stmt
        xs <- P.many1 (stmt_break >> as_stmt)
        return (x:xs)
        
        
    assign_first_body =
      do
        x <- as_stmt
        (do
           stmt_break
           xs <- unpack_rest_body <|> assign_first_body
           return (x:xs))
          <|> return [x]
          
          
    unpack_rest_body =
      do
        x <- reversible_unpack_stmt
        xs <- P.many (stmt_break >> as_stmt)
        return (x:xs)
  
  
-- | Parse an expression with binary operations
rhs :: Parser Rval
rhs =
  try import_expr <|> or_expr

  
-- |
import_expr :: Parser Rval
import_expr =
  do
    P.string "from" 
    P.space
    spaces
    x <- raddress
    return (Import x)
    
    
bracket :: Parser Rval
bracket =
  P.between (P.char '(') (P.char ')') (trim rhs)

  
raddress :: Parser Rval
raddress =
  first >>= rest
    where
      next x =
        try
          (do 
             spaces
             (bracket >>= return . Apply x)
               <|> (name >>= return . Get x))
      
      
      rest x =
        (next x >>= rest)
          <|> return x
      
      
      first =
        string
          <|> bracket
          <|> number
          <|> structure
          <|> (name >>= return . GetSelf)
          <|> (fieldId >>= return . GetEnv)
      
      
-- | Parse an unpack statement
unpack_stmt :: Parser Stmt
unpack_stmt = 
  do
    P.char '*'
    x <- raddress 
    return (Unpack x)
    
    
-- | Parse an assign statement
assign_stmt :: Parser Stmt
assign_stmt =
  do
    x <- laddress
    trim (P.char '=')
    P.option
      (Declare x)
      (do
         y <- rhs
         return (Address x `Set` y))

         
-- | Parse an assign statement
destruct_stmt :: Parser Stmt
destruct_stmt =
  do
    x <- destructure
    trim (P.char '=')
    y <- rhs
    return (x `Set` y)
    
    
-- | Parse an cmd statement
run_stmt :: Parser Stmt
run_stmt = 
  do
    x <- rhs
    return (Run x)
    
    
-- | Parse any statement
stmt :: Parser Stmt
stmt =
  unpack_stmt
    <|> try assign_stmt
    <|> try destruct_stmt
    <|> run_stmt
    <?> "statement"
      

-- | Parse a curly-brace wrapped sequence of statements
structure :: Parser Rval
structure =
  P.between
    (P.char '{')
    (P.char '}')
    (trim $ P.sepBy stmt stmt_break)
    >>= return . Structure
    
    
-- | Parse an unary operator
unop :: Parser Rval
unop =
  do
    s <- unop_symbol
    spaces
    x <- raddress
    return (Unop s x)
    where
      unop_symbol =
        (P.char '-' >> return Neg)
          <|> (P.char '!' >> return Not)

          
or_expr :: Parser Rval
or_expr =
  P.chainl1 and_expr (try $ trim or_ops)
    where
      or_ops =
        P.char '|' >> return (Binop Or)

      
and_expr :: Parser Rval
and_expr =
  P.chainl1 cmp_expr (try $ trim and_ops)
    where
      and_ops =
        P.char '&' >> return (Binop And)

        
cmp_expr :: Parser Rval
cmp_expr = 
  do
    a <- add_expr
    (do
       s <- try (trim cmp_ops)
       b <- add_expr
       return (s a b))
      <|> return a
  where
    cmp_ops =
      try (P.string "==" >> return (Binop Eq))
        <|> try (P.string "!=" >> return (Binop Ne))
        <|> try (P.string ">=" >> return (Binop Ge))
        <|> try (P.string "<=" >> return (Binop Le))
        <|> (P.char '>' >> return (Binop Gt))
        <|> (P.char '<' >> return (Binop Lt))
   
   
add_expr :: Parser Rval
add_expr =
  P.chainl1 mul_expr (try $ trim add_ops)
    where
      add_ops =
        (P.char '+' >> return (Binop Add))
          <|> (P.char '-' >> return (Binop Sub))


mul_expr :: Parser Rval
mul_expr =
  P.chainl1 pow_expr (try $ trim mul_ops)
    where
      mul_ops =
        (P.char '*' >> return (Binop Prod))
          <|> (P.char '/' >> return (Binop Div))


pow_expr :: Parser Rval
pow_expr =
  P.chainl1 term (try $ trim pow_ops)
    where
      pow_ops =
        P.char '^' >> return (Binop Pow)
      
      
      term =
        unop <|> raddress
    
    
-- | Parse a top-level sequence of statements
program :: Parser Rval
program =
  do
    xs <- trim (P.sepBy1 stmt stmt_break)
    case xs of
      [Run r] ->
        return r
        
      _ ->
        return (Structure xs)


