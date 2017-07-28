module Parser
  ( float
  , decimal
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , field
  , name
  , selection
  , lhs
  , laddress
  , destructure
  , rhs
  , unop
  , and_expr
  , raddress
  , structure
  , program
  )
  where
  
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
import Data.List.NonEmpty( NonEmpty(..), toList )
  
  
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
field :: Parser FieldId
field =
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
    field
    
    
lhs :: Parser Pattern
lhs =
  (Address <$> laddress) <|> destructure <?> "lhs"

      
laddress :: Parser Lval
laddress =
  first >>= rest
    where
      first =
        (name >>= return . InSelf)
          <|> (field >>= return . InEnv)
      
      
      next x =
        try (spaces >> name >>= return . In x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x

      
-- | Parse an statement break
stmt_break =
   try (trim (P.char ';'))
   
   
-- | Parse a destructuring lval assignment
lstmt0 :: Parser Lstmt0
lstmt0 = 
  do
    x <- selection_pattern0
    trim (P.char '=')
    y <- lhs
    return (x `As` y)
    
    
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
      unpack_first_body
        <|> lassign_packed_first_body
        <|> lassign_first_body
        <?> "lstmt"
  
    
    unpack_first_body =
      do
        try (P.string "...")
        xs <- P.many (stmt_break >> lstmt0)
        return (UnpackRemaining xs)
        
        
    lassign_packed_first_body =
      do
        x <- selection_pattern1
        trim (P.char '=')
        y <- lhs
        xs <- P.many (stmt_break >> lstmt0)
        return ((x `AsP` y) :!! xs)
        
        
    lassign_first_body =
      do
        x <- lstmt0
        mb <- P.optionMaybe (stmt_break >> destructure_body)
        return (maybe (Only x) (x :||) mb)
  
  
-- | Parse a selection
selection :: Parser Selection
selection =
  first >>= rest
    where
      first =
        name >>= return . SelectSelf
  

      next x =
        try (spaces >> name >>= return . Select x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x
          
          
selection_pattern :: Parser SelectionPattern
selection_pattern =
  (Packed <$> selection_pattern1)
    <|> (Unpacked <$> selection_pattern0)
    
  
-- | Parse a non-packed selection pattern
selection_pattern0 :: Parser SelectionPattern0
selection_pattern0 =
  (AddressS <$> selection) <|> description
  
  
match_stmt0 :: Parser Match0
match_stmt0 =
  do
    x <- selection_pattern
    trim (P.char '=')
    y <- selection_pattern0
    return (x `Match` y)
  

description :: Parser SelectionPattern0
description =
  P.between
    (P.char '{')
    (P.char '}')
    (trim description_body)
    >>= return . Description
    where
      description_body =
        do
          x <- match_stmt0
          xs <- P.many (stmt_break >> match_stmt0)
          return (x:|xs)
        
        
-- | ...packed selection pattern
selection_pattern1 :: Parser SelectionPattern1
selection_pattern1 =
  P.between
    (P.char '{')
    (P.char '}')
    (trim descriptionP_body)
    >>= return . DescriptionP
  where
    descriptionP_body =
      repack_first_body
        <|> match_packed_first_body
        <|> match_first_body
        <?> "descriptionP"

        
    repack_first_body =
      do
        try (P.string "...")
        xs <- P.many (stmt_break >> match_stmt0)
        return (PackRemaining xs)
        
    match_packed_first_body =
      do
        x <- selection_pattern
        trim (P.char '=')
        y <- selection_pattern1
        xs <- P.many (stmt_break >> match_stmt0)
        return ((x `MatchP` y) :!: xs)
        
        
    match_first_body =
      do
        x <- match_stmt0
        stmt_break
        a <- descriptionP_body
        return (x :|: a)
            
    
        
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
          <|> (field >>= return . GetEnv)
          <?> "rvalue"
    
    
-- | Parse an assign statement
set_stmt :: Parser Stmt
set_stmt =
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
    
    
-- | Parse an eval statement
run_stmt :: Parser Stmt
run_stmt = 
  do
    x <- rhs
    return (Run x)
    
    
-- | Parse any statement
stmt :: Parser Stmt
stmt =
  try set_stmt
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
  P.chainl1 and_expr (try (trim or_ops))
    where
      or_ops =
        P.char '|' >> return (Binop Or)

      
and_expr :: Parser Rval
and_expr =
  P.chainl1 cmp_expr (try (trim and_ops))
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
  P.chainl1 mul_expr (try (trim add_ops))
    where
      add_ops =
        (P.char '+' >> return (Binop Add))
          <|> (P.char '-' >> return (Binop Sub))


mul_expr :: Parser Rval
mul_expr =
  P.chainl1 pow_expr (try (trim mul_ops))
    where
      mul_ops =
        (P.char '*' >> return (Binop Prod))
          <|> (P.char '/' >> return (Binop Div))


pow_expr :: Parser Rval
pow_expr =
  P.chainl1 term (try (trim pow_ops))
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


