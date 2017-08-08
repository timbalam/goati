module Parser
  ( decFloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , field
  , path
  , selection
  , lhs
  , laddress
  , destructure
  , rhs
  , unop
  , orExpr
  , raddress
  , structure
  , program
  )
  where
  
import Types.Parser
import Types.Util.List

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


class ReadMy a where
  readMy :: String -> Parser a
  
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  P.sepBy1 d (P.optional (P.char '_'))
    
    
-- | Parser for valid decimal or floating point number
decFloat :: Parser Rval
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
        (do
          ys <- integer P.digit
          expNext (xs ++ [y] ++ ys)   -- frac exp
            <|> (return . NumberLit . read) (xs ++ [y] ++ ys))
                                      -- frac
          <|> (return . NumberLit . read) (xs ++ [y, '0'])
                                      -- frac
          
    expNext xs =
      do 
        e <- P.oneOf "eE"
        sgn <- P.option [] (P.oneOf "+-" >>= return . (:[]))
        ys <- integer P.digit
        (return . NumberLit . read) (xs ++ e:sgn ++ ys)
    
    
-- | Parser for valid binary number
binary :: Parser Rval
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parser for valid octal number
octal :: Parser Rval
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parser for valid hexidecimal number
hexidecimal :: Parser Rval
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
    
    
-- | Parser that parses whitespace
spaces =
  P.spaces
    
    
-- | Parser for valid numeric value
number :: Parser Rval
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
string :: Parser Rval
string =
  do
    x <- stringFragment
    xs <- P.many stringFragment
    return (StringLit (x :| xs))
    where
      stringFragment =
        P.between
          (P.char '"')
          (P.char '"' >> spaces)
          (P.many (P.noneOf "\"\\" <|> escapedChars))

          
-- | Parser that succeeds when consuming a valid identifier string.
field :: Parser FieldId
field =
  do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    return (Field (x:xs))

-- | Parse a valid node path
path :: Parser FieldId
path =
  do
    P.char '.'
    spaces
    field 
    
      
-- | Parse an statement break
stmtBreak =
  P.char ';' >> spaces
    
    
-- | Parse a set statement
setStmt :: Parser Stmt
setStmt =
  do
    x <- laddress
    (do
      P.char '='
      spaces
      (do
        y <- rhs
        return (Address x `Set` y))
        <|> return (Declare x))
      <|> return (SetPun x)
        

-- | Parse a destructuring statement
destructureStmt :: Parser Stmt
destructureStmt =
  do
    x <- destructure
    P.char '='
    spaces
    y <- rhs
    return (x `Set` y)
    
    
-- | Parse an eval statement
runStmt :: Parser Stmt
runStmt = 
  do
    try (P.string "#run" >> P.space)
    spaces
    y <- rhs
    return (Run y)
    
    
-- | Parse any statement
stmt :: Parser Stmt
stmt =
  runStmt                 -- '#' ...
    <|> setStmt           -- '.' alpha ...
                          -- alpha ...
    <|> destructureStmt   -- '{' ...
    <?> "statement"

      
-- | Parse an addressable lhs pattern
laddress :: Parser Lval
laddress =
  first >>= rest
    where
      first =
        (path >>= return . InSelf)        -- '.'
          <|> (field >>= return . InEnv)  -- alpha
      
      
      next x =
        path >>= return . In x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
          
    
-- | Parse a destructuring lhs pattern
destructure :: Parser Pattern
destructure =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    destructureBody
    >>= return . Destructure
  where
  
    destructureBody :: Parser DestructureBody
    destructureBody =
      unpackFirstBody           -- "..."
        <|> describeFirstBody   -- '{' ...
        <|> setFirstBody        -- '.' alpha ...
                                -- alpha ..
        <?> "destructuring statement"
  
    
    unpackFirstBody =
      do
        try (P.string "...")
        spaces
        xs <- P.many (stmtBreak >> lstmt)
        return ([] :<: Left (UnpackRemaining :>: xs))
        
        
    describeFirstBody =
      do
        x <- descriptionP
        P.char '='
        spaces
        y <- lhs
        case x of
          Packed d ->
            do
              xs <- P.many (stmtBreak >> lstmt)
              return ([] :<: Left ((d `AsP` y) :>: xs))
            
          Plain d ->
            do
              let x = d `As` y
              mb <- P.optionMaybe (stmtBreak >> destructureBody)
              case mb of
                Nothing ->
                  return ([] :<: Right x)
                  
                Just (xs :<: a) ->
                  return (x : xs :<: a)
        
        
    setFirstBody =
      do
        x <- setLstmt
        mb <- P.optionMaybe (stmtBreak >> destructureBody)
        case mb of
          Nothing ->
            return ([] :<: Right x)
            
          Just (xs :<: a) ->
            return (x : xs :<: a)

            
-- | Parse an lval assignment
setLstmt :: Parser Lstmt0
setLstmt = 
  (do                                   -- '.' alpha
    x <- selection
    (do
      P.char '='
      spaces
      y <- lhs
      return (AddressS x `As` y))
      <|> return (AsPun (toLval x)))
    <|> (laddress >>= return . AsPun)   -- alpha
        
  where
    toLval :: Selection -> Lval
    toLval (SelectSelf x) = InSelf x
    toLval (s `Select` x) = toLval s `In` x
    
    
-- | Parse a destructuring lval assignment
describeLstmt :: Parser Lstmt0
describeLstmt =
  do
    x <- description
    P.char '='
    spaces
    y <- lhs
    return (x `As` y)
        
        
-- | Parse an unpacked lstmt
lstmt :: Parser Lstmt0
lstmt = 
  describeLstmt   -- '{' ...
    <|> setLstmt  -- '.' ...
                  -- alpha ...
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: Parser Pattern
lhs =
  (laddress >>= return . Address)
    <|> destructure
    <?> "lhs"
  
  
-- | Parse a selection
selection :: Parser Selection
selection =
  first >>= rest
    where
      first =
        path >>= return . SelectSelf
  

      next x =
        path >>= return . Select x
      
      
      rest x =
        (next x >>= rest)
          <|> return x
        
        
-- | Description
descriptionP :: Parser SelectionPattern
descriptionP =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    (descriptionPBody >>= return . either (Packed . DescriptionP) (Plain . Description))
  where
        
    descriptionPBody ::
      Parser (Either Description1Body Description0Body)
    descriptionPBody =
      repackFirstBody
        <|> matchFirstBody
        <?> "descriptionP"

        
    repackFirstBody =
      do
        try (P.string "...")
        spaces
        xs <- P.many (stmtBreak >> matchStmt)
        (return . Left)
          ([] :<: (RepackRemaining :>: xs))
        
        
    matchFirstBody =
      do
        e <- matchStmtP
        case e of
          Right x ->
            do
              mb <- P.optionMaybe (stmtBreak >> descriptionPBody)
              case mb of 
                Nothing ->
                  return (Right (x :| []))
                  
                Just (Right d) ->
                  return (Right (x :| toList d))
                  
                Just (Left (xs :<: a)) ->
                  return (Left ((x:xs) :<: a))
                
          Left x ->
            do
              xs <- P.many (stmtBreak >> matchStmt)
              return (Left ([] :<: (x :>: xs)))
        
        
-- | Parse a selection matching a pattern
setMatchStmtP :: Parser (Either Match1 Match0)
setMatchStmtP =
  do
    x <- selection
    (do
      P.char '='
      spaces
      y <- selectionPatternP
      case y of
        Packed p ->
          return (Left (Plain (AddressS x) `MatchP` p))
          
        Plain p ->
          return (Right (Plain (AddressS x) `Match` p)))
          
      <|> return (Right (MatchPun x))
      
   
-- | Parse a description matching a pattern   
describeMatchStmtP :: Parser (Either Match1 Match0)
describeMatchStmtP =
  do
    x <- descriptionP
    P.char '='
    spaces
    y <- selectionPatternP
    case y of
      Packed p ->
        return (Left (x `MatchP` p))
        
      Plain p ->
        return (Right (x `Match` p))
        
        
-- | Parse a match statement
matchStmtP :: Parser (Either Match1 Match0)
matchStmtP =
  setMatchStmtP             -- '.'
                            -- alpha
    <|> describeMatchStmtP  -- '{'
        
          
-- | Parse a selection pattern
selectionPatternP :: Parser SelectionPattern
selectionPatternP =
  (selection >>= return . Plain . AddressS)   -- '.'
    <|> descriptionP                          -- '{'
    

-- | Non-packed description
description :: Parser SelectionPattern0
description =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    description_body
    >>= return . Description
    where
      description_body =
        do
          x <- matchStmt
          xs <- P.many (stmtBreak >> matchStmt)
          return (x:|xs)
  
  
-- | Parse a non-packed selection pattern
selectionPattern :: Parser SelectionPattern0
selectionPattern =
  (selection >>= return . AddressS)
    <|> description

  
-- | Parse a selection matching a non-packed pattern
setMatchStmt :: Parser Match0
setMatchStmt =
  do
    x <- selection
    (do 
      P.char '='
      spaces
      y <- selectionPattern
      return (Plain (AddressS x) `Match` y))
      <|> return (MatchPun x)
      
    
-- | Parse a description matching a non-packed pattern
describeMatchStmt :: Parser Match0
describeMatchStmt =
  do
    x <- descriptionP
    P.char '='
    spaces
    y <- selectionPattern
    return (x `Match` y)
    
    
-- | Parse a non-packed match statement
matchStmt :: Parser Match0
matchStmt =
  setMatchStmt              -- '.'
    <|> describeMatchStmt   -- '{'
            
    
-- | Parse an expression with binary operations
rhs :: Parser Rval
rhs =
  importExpr    -- '#' ...
    <|> orExpr  -- '!' ...
                -- '-' ...
                -- '"' ...
                -- '(' ...
                -- digit ...
                -- '{' ...
                -- '.' ...
                -- alpha ...

  
-- | Parse an import expression
importExpr :: Parser Rval
importExpr =
  do
    try (P.string "#from" >> P.space)
    spaces
    x <- raddress
    return (Import x)
    
    
bracket :: Parser Rval
bracket =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    rhs

  
raddress :: Parser Rval
raddress =
  first >>= rest
    where
      next x =
        (bracket >>= return . Apply x)
          <|> (path >>= return . Get x)
      
      
      rest x =
        (next x >>= rest)
          <|> return x
      
      
      first =
        string                              -- '"' ...
          <|> bracket                       -- '(' ...
          <|> number                        -- digit ...
          <|> structure                     -- '{' ...
          <|> (path >>= return . GetSelf)   -- '.' ...
          <|> (field >>= return . GetEnv)   -- alpha ...
          <?> "rvalue"
      

-- | Parse a curly-brace wrapped sequence of statements
structure :: Parser Rval
structure =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)
    structureBody
    >>= return . Structure
    where
      structureBody :: Parser StructureBody
      structureBody =
        packFirst                       -- "..."
          <|> stmtFirst                 -- '#' ...
                                        -- '.' alpha ...
                                        -- '{' ...
                                        -- alpha ...
          <|> return ([] :<: Nothing)   -- '}'
          <?> "statement"
          
          
      packFirst =
        do
          try (P.string "...")
          spaces
          xs <- P.many (stmtBreak >> stmt)
          return ([] :<: Just (PackEnv :>: xs))
        
      stmtFirst =
        do
          x <- stmt
          mb <- P.optionMaybe (stmtBreak >> structureBody)
          case mb of
            Nothing ->
              return ([x] :<: Nothing)
              
            Just (xs :<: a) ->
              return ((x:xs) :<: a)
    
    
-- | Parse an unary operation
unop :: Parser Rval
unop =
  do
    s <- op
    x <- raddress
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orExpr :: Parser Rval
orExpr =
  P.chainl1 andExpr orOp
    where
      orOp =
        P.char '|' >> spaces >> return (Binop Or)

      
andExpr :: Parser Rval
andExpr =
  P.chainl1 cmpExpr andOp
    where
      andOp =
        P.char '&' >> spaces >> return (Binop And)

        
cmpExpr :: Parser Rval
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
   
   
addExpr :: Parser Rval
addExpr =
  P.chainl1 mulExpr addOp
    where
      addOp =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulExpr :: Parser Rval
mulExpr =
  P.chainl1 powExpr mulOp
    where
      mulOp =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powExpr :: Parser Rval
powExpr =
  P.chainl1 term powOp
    where
      powOp =
        P.char '^' >> spaces >> return (Binop Pow)
      
      
      term =
        unop            -- '!'
                        -- '-'
          <|> raddress  -- '"'
                        -- '('
                        -- digit
                        -- '{'
                        -- '.'
                        -- alpha
    
    
-- | Parse a top-level sequence of statements
program :: Parser Rval
program =
  do
    xs <- P.sepBy1 stmt stmtBreak
    P.eof
    case xs of
      [Run r] ->
        return r
      
      _ ->
        return (Structure (xs :<: Nothing))


