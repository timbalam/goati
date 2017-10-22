module Parser
  ( decFloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
<<<<<<< HEAD
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

=======
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
>>>>>>> unpack_dots
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
<<<<<<< HEAD
=======
import Data.List.NonEmpty( NonEmpty(..), toList )


class ReadMy a where
  readMy :: String -> Parser a
>>>>>>> unpack_dots
  
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
<<<<<<< HEAD
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
=======
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
>>>>>>> unpack_dots
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parser for valid octal number
<<<<<<< HEAD
octal :: Parser Rval
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . NumberLit . oct2dig
=======
octal :: Parser (Expr a)
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
>>>>>>> unpack_dots
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parser for valid hexidecimal number
<<<<<<< HEAD
hexidecimal :: Parser Rval
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . NumberLit . hex2dig
=======
hexidecimal :: Parser (Expr a)
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
>>>>>>> unpack_dots
  where 
    hex2dig x =
      fst (readHex x !! 0)
    
    
<<<<<<< HEAD
-- | Parser for valid numeric value
number :: Parser Rval
number =
  binary
    <|> octal
    <|> hexidecimal
    <|> try float
    <|> decimal
    <?> "number"
=======
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
>>>>>>> unpack_dots

    
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
<<<<<<< HEAD
string :: Parser Rval
string =
  P.sepBy1 string_fragment spaces >>= return . StringLit . concat
    where
      string_fragment =
        P.between
          (P.char '"')
          (P.char '"')
=======
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
>>>>>>> unpack_dots
          (P.many (P.noneOf "\"\\" <|> escapedChars))

          
-- | Parser that succeeds when consuming a valid identifier string.
<<<<<<< HEAD
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
=======
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
setStmt :: Parser (Stmt T.Text)
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
destructureStmt :: Parser (Stmt T.Text)
destructureStmt =
  do
    x <- destructure
    P.char '='
    spaces
    y <- rhs
    return (x `Set` y)
    
    
-- | Parse any statement
stmt :: Parser (Stmt T.Text)
stmt =
  setStmt                 -- '.' alpha ...
                          -- alpha ...
    <|> destructureStmt   -- '{' ...
    <?> "statement"

      
-- | Parse an addressable lhs pattern
path :: Parser (Path T.Text)
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
destructure :: Parser (SetExpr T.Text)
destructure =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    body
    >>= return . SetBlock
  where
  
    body :: Parser (BlockExpr (MatchStmt T.Text))
    body =
      unpackStmt              -- "..."
        <|> 
          (do
            x <- matchStmt  -- '{' ...
                            -- '.' alpha ...
                            -- alpha ..
            m <- P.optionMaybe (stmtBreak >> body)
            case m of
              Nothing ->
                return (x :& [])
                
              Just (Open xs) ->
                return (Open (x:xs))
                
              Just (y :& ys) ->
                return (x :& (y:ys)))
        <?> "destructuring statement"
    
    unpackStmt =
      do
        try (P.string "...")
        spaces
        return (Open [])

            
-- | Parse an lval assignment
matchPath :: Parser (MatchStmt T.Text)
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
matchBlock :: Parser (MatchStmt T.Text)
matchBlock =
  do
    x <- blockPattern
    P.char '='
    spaces
    y <- lhs
    return (x `Match` y)
        
        
-- | Parse a match stmt
matchStmt :: Parser (MatchStmt T.Text)
matchStmt = 
  matchBlock       -- '{' ...
    <|> matchPath  -- '.' ...
                   -- alpha ...
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser (SetExpr T.Text)
lhs =
  (path >>= return . SetPath)
    <|> destructure
    <?> "lhs"
  
  
-- | Parse a selection
pathPattern :: Parser (PathPattern T.Text)
pathPattern =
  first >>= rest
    where
      first =
        field >>= return . SelfAtP
  

      next x =
        field >>= return . AtP x
      
>>>>>>> unpack_dots
      
      rest x =
        (next x >>= rest)
          <|> return x
        
        
-- | Description
blockPattern :: Parser (PatternExpr T.Text)
blockPattern =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (body >>= return . AsBlock)
  where
        
    body ::
      Parser (BlockExpr (AsStmt T.Text))
    body =
      repackStmt
        <|> 
          (do
            x <- asStmt
            m <- P.optionMaybe (stmtBreak >> body)
            case m of
              Nothing ->
                return (x :& [])
                
              Just (Open xs) ->
                return (Open (x:xs))
                
              Just (y :& ys) ->
                return (x :& (y:ys)))
        <?> "blockPattern"

        
    repackStmt =
      do
        try (P.string "...")
        spaces
        return (Open [])
        
        
-- | Parse a match to a path pattern
asPathStmt :: Parser (AsStmt T.Text)
asPathStmt =
  do
    x <- pathPattern
    (do
      P.char '='
      spaces
      y <- patternExpr
      return (AsPath x `As` y))
      <|> return (AsPun x)
      
<<<<<<< HEAD
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
=======
   
-- | Parse a match to a block pattern
asBlockStmt :: Parser (AsStmt T.Text)
asBlockStmt =
  do
    x <- blockPattern
    P.char '='
    spaces
    y <- patternExpr
    return (x `As` y)
        
        
-- | Parse an as statement
asStmt :: Parser (AsStmt T.Text)
asStmt =
  asPathStmt          -- '.'
                      -- alpha
    <|> asBlockStmt   -- '{'
        
          
-- | Parse a selection pattern
patternExpr :: Parser (PatternExpr T.Text)
patternExpr =
  (pathPattern >>= return . AsPath)   -- '.'
    <|> blockPattern                  -- '{'
    
    
-- | Parse an expression with binary operations
rhs :: Parser (Expr T.Text)
rhs =
  orExpr        -- '!' ...
                -- '-' ...
                -- '"' ...
                -- '(' ...
                -- digit ...
                -- '{' ...
                -- '.' ...
                -- alpha ...

    
bracket :: Parser (Expr T.Text)
bracket =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    rhs

  
pathExpr :: Parser (Expr T.Text)
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
block :: Parser (Expr T.Text)
block =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (do
      (body >>= return . Block)
        <|> return EmptyBlock
        <?> "statement")
    where
      body :: Parser (BlockExpr (Stmt T.Text))
      body =
        packStmt                       -- "..."
          <|> 
            (do 
              x <- stmt                -- '#' ...
                                       -- '.' alpha ...
                                       -- '{' ...
                                       -- alpha ...
              ys <- P.optionMaybe (stmtBreak >> body)
              case ys of
                Nothing ->
                  return (x :& [])
                  
                Just (Open xs) ->
                  return (Open (x:xs))
                    
                Just (y :& ys) ->
                    return (x :& (y:ys)))
          
          
      packStmt =
        do
          try (P.string "...")
          spaces
          return (Open [])
    
    
-- | Parse an unary operation
unop :: Parser (Expr T.Text)
unop =
  do
    s <- op
    x <- pathExpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orExpr :: Parser (Expr T.Text)
orExpr =
  P.chainl1 andExpr orOp
    where
      orOp =
        P.char '|' >> spaces >> return (Binop Or)

      
andExpr :: Parser (Expr T.Text)
andExpr =
  P.chainl1 cmpExpr andOp
    where
      andOp =
        P.char '&' >> spaces >> return (Binop And)

        
cmpExpr :: Parser (Expr T.Text)
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
   
   
addExpr :: Parser (Expr T.Text)
addExpr =
  P.chainl1 mulExpr addOp
    where
      addOp =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulExpr :: Parser (Expr T.Text)
mulExpr =
  P.chainl1 powExpr mulOp
    where
      mulOp =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powExpr :: Parser (Expr T.Text)
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
program :: Parser (BlockExpr T.Text)
program =
  do
    x <- stmt
    stmtBreak
    xs <- P.sepBy stmt stmtBreak
    P.eof
    return (x :& xs)
>>>>>>> unpack_dots


