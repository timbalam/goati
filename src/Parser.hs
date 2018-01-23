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
  , var
  , path
  , unop
  , stmt
  , matchstmt
  , lhs
  , rhs
  , pathexpr
  , program
  , SymParser
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
import Text.Parsec.Text ( GenParser )
import Numeric( readHex, readOct )
import Control.Applicative( liftA2 )
import Data.Foldable( foldl', concat, toList )
import Data.List.NonEmpty( NonEmpty(..), nonEmpty )
import Data.Semigroup( (<>) )
import Control.Monad.Free


-- | Alias for parser type
type SymParser = GenParser Id

  
-- | Parse a sequence of underscore spaced digits
integer :: GenParser u Char -> GenParser u String
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
  
  
-- | Parse a single decimal point / field accessor (disambiguated from extension dots)
point :: GenParser u Char
point = try (P.char '.' <* P.notFollowedBy (P.char '.'))

  
-- | Parse a block extension separator
extendbreak :: GenParser u ()
extendbreak =
  try (P.string "..." <* P.notFollowedBy (P.char '.')) >> spaces
    
    
-- | Parser for valid decimal or floating point number
decfloat :: GenParser u Syntax
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
    
    
-- | Parse a valid binary number
binary :: GenParser u Syntax
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: GenParser u Syntax
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: GenParser u Syntax
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
      
      
      
-- | Parse a comment
comment :: GenParser u T.Text
comment = do
  try (P.string "//")
  s <- P.manyTill P.anyChar (try ((P.endOfLine >> return ()) <|> P.eof))
  return (T.pack s)
    
    
-- | Parse whitespace and comments
spaces = P.spaces >> P.optional (comment >> spaces)
    
    
-- | Parse any valid numeric value
number :: GenParser u Syntax
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number")
    <* spaces

    
-- | Parse an escaped character.
escapedchars :: GenParser u Char
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

          
-- | Parse a double-quote wrapped string.
string :: GenParser u Syntax
string =
  StringLit . T.pack <$> stringfragment

  
stringfragment :: GenParser u String
stringfragment =
  P.between
    (P.char '"')
    (P.char '"' >> spaces)
    (P.many (P.noneOf "\"\\" <|> escapedchars))

          
-- | Parse a valid identifier string.
ident :: GenParser u String
ident =
  do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    return (x:xs)
    

identpath :: GenParser u String
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
symbol :: GenParser u Symbol
symbol = do
  P.char '\''
  S . T.pack <$> ident
    

  
-- | Parse a valid field accessor
field :: GenParser u Tag
field =
  do
    point
    spaces
    (Symbol <$> parens symbol)
      <|> (Label . T.pack <$> ident)
      
    
-- | Parse an addressable lhs pattern 
path :: GenParser u a -> GenParser u (Path a)
path first = first >>= rest . Pure
  where
    rest x =
      (field >>= rest . Free . At x)
        <|> return x
        
        
var :: GenParser u Var
var =
  (Pub <$> field)
    <|> (Priv . T.pack <$> ident)
    
    
-- | Parse an statement break
stmtbreak :: GenParser u ()
stmtbreak =
  P.char ';' >> spaces
  
  
-- | Parse different bracket types
braces :: GenParser u a -> GenParser u a
braces =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)

    
parens :: GenParser u a -> GenParser u a
parens =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    

staples :: GenParser u a -> GenParser u a
staples =
  P.between
    (P.char '[' >> spaces)
    (P.char ']' >> spaces)
    
  
blockexpr :: GenParser u a -> GenParser u [a]
blockexpr stmt = braces (P.sepEndBy stmt stmtbreak) 


-- | Parse a symbol declaration
declsym :: SymParser Stmt
declsym = DeclSym <$> symbol <*> P.getState <* P.modifyState succ

    
-- | Parse a set statement
setstmt :: SymParser Stmt
setstmt =
  do
    l <- path var
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
destructurestmt :: SymParser Stmt
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
stmt :: SymParser Stmt
stmt =
  declsym                 -- '\'' alpha
    <|> setstmt           -- '.' alpha ...
                          -- alpha ...
    <|> destructurestmt   -- '{' ...
    <?> "statement"
        
        
-- | Parse a match stmt
matchstmt :: GenParser u MatchStmt
matchstmt =
  (do
    r <- path field                         -- '.' alpha
    (do
      P.char '='
      spaces
      l <- lhs
      return (r `Match` l))
      <|> (return . MatchPun) (Pub <$> r))
    <|> (path var >>= return . MatchPun)    -- alpha
                    
                    
-- | Parse a valid lhs pattern for an assignment
lhs :: GenParser u SetExpr
lhs = 
  (path var >>= decomp . SetPath)
    <|> (blockexpr matchstmt >>= decomp . SetBlock)
    <?> "lhs"
  where
    decomp s =
      (blockexpr matchstmt >>= decomp . SetDecomp s)
      <|> return s
    
    
-- | Parse an expression with binary operations
rhs :: SymParser Syntax
rhs =
    orexpr    -- '!' ...
              -- '-' ...
              -- '"' ...
              -- '(' ...
              -- digit ...
              -- '{' ...
              -- '.' alpha ...
              -- alpha ...

  
pathexpr :: SymParser Syntax
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
        <|> (Var <$> var)               -- '.' alpha ...
                                        -- alpha ...
                                        -- '#' '"' ...
        <?> "value"
    
    
-- | Parse an unary operation
unop :: SymParser Syntax
unop =
  do
    s <- op
    x <- pathexpr
    return (Unop s x)
    where
      op =
        (P.char '-' >> spaces >> return Neg)        -- '-' ...
          <|> (P.char '!' >> spaces >> return Not)  -- '!' ...

          
orexpr :: SymParser Syntax
orexpr =
  P.chainl1 andexpr op
    where
      op =
        P.char '|' >> spaces >> return (Binop Or)

      
andexpr :: SymParser Syntax
andexpr =
  P.chainl1 cmpexpr op
    where
      op =
        P.char '&' >> spaces >> return (Binop And)

        
cmpexpr :: SymParser Syntax
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
   
   
addexpr :: SymParser Syntax
addexpr =
  P.chainl1 mulexpr op
    where
      op =
        (P.char '+' >> spaces >> return (Binop Add))
          <|> (P.char '-' >> spaces >> return (Binop Sub))


mulexpr :: SymParser Syntax
mulexpr =
  P.chainl1 powexpr op
    where
      op =
        (P.char '*' >> spaces >> return (Binop Prod))
          <|> (P.char '/' >> spaces >> return (Binop Div))


powexpr :: SymParser Syntax
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
program :: SymParser (NonEmpty Stmt)
program =
  (do
    x <- stmt
    (do
      stmtbreak
      xs <- P.sepEndBy stmt stmtbreak
      return (x:|xs))
      <|> return (pure x))
    <* P.eof

