{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes, MultiParamTypeClasses #-}

-- | Parsers for my syntax types

module My.Parser.Class
  ( decfloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , pathexpr
  , Parser, parse
  , ShowMy(..)
  , ReadMy(..)
  )
  where
  
--import qualified My.Types.Parser.Class as C
import My.Types.Parser.Class
  ( Lit(..), Op(..), Self(..), Local(..), Extern(..), Field(..)
  , Extend(..), Block(..), Tuple(..), Program(..)
  , Let(..), RecStmt(..), TupStmt(..), Patt, Syntax, Member
  , LocalPath, RelPath, VarPath
  )
import My.Types.Parser
  ( Ident(..), Key(..), Import(..)
  , Unop(..), Binop(..)
  )
import My.Parser
  ( ShowMy(..), ReadMy(..)
  , comment, spaces, point, stringfragment, escapedchars, identpath
  , eqsep, semicolonsep, ellipsissep, commasep
  , braces, parens, staples
  , readOr, readAnd, readEq, readNe, readLt, readGt, readLe
  , readGe, readAdd, readSub, readProd, readDiv, readPow
  , readNeg, readNot
  )
import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec ((<|>), (<?>), try, parse)
import Text.Parsec.Text  (Parser)
import Numeric (readHex, readOct)
import Control.Applicative (liftA2)
import Data.Char (showLitChar)
import Data.Foldable (foldl', concat, toList)
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import Data.Semigroup ((<>), option)
import Data.Function ((&))
import Data.Bifunctor (bimap)
import Control.Monad.State
     
    
-- | Parse any valid numeric literal
number :: Lit r => Parser r
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number literal")
    <* spaces
    
    
-- | Parse a valid binary number
binary :: Lit r => Parser r
binary =
  do
    try (P.string "0b")
    int_ . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: Lit r => Parser r
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . int_ . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: Lit r => Parser r
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . int_ . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
  
  
  
-- | Parse a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
   
    
-- | Parser for valid decimal or floating point number
decfloat :: Lit r => Parser r
decfloat =
  prefixed
    <|> unprefixed
  where
    prefixed =
      do
        try (P.string "0d")
        int_ . read <$> integer P.digit
        
    unprefixed =
      do
        xs <- integer P.digit
        fracnext xs                               -- int frac
                                                  -- int frac exp
          <|> expnext xs                          -- int exp
          <|> (return . int_) (read xs)   -- int
          
    fracnext xs =
      do 
        y <- point
        m <- P.optionMaybe (integer P.digit)
        case m of
          Nothing ->
            -- frac
            (return . num_ . read) (xs ++ [y, '0'])
            
          Just ys ->
            expnext (xs ++ [y] ++ ys)   -- frac exp
              <|>
                (return . num_ . read) (xs ++ [y] ++ ys)
                                      -- frac
          
    expnext xs =
      do 
        e <- P.oneOf "eE"
        sgn <- P.option [] (P.oneOf "+-" >>= return . pure)
        ys <- integer P.digit
        (return . num_ . read) (xs ++ e:sgn ++ ys)


-- | Parse a double-quote wrapped string literal
string :: Lit r => Parser r
string =
  str_ . T.pack <$> stringfragment <?> "string literal"
  
  
lit :: Lit r => Parser r
lit = number <|> string

  
-- | Parse a variable name
var :: (Local r, Self r, Extern r) => Parser r
var = (local_ <$> readsMy)  -- alpha
  <|> (self_ <$> readsMy)   -- '.' alpha
  <|> (import_ <$> readsMy) -- '@'
  
  
-- | Parse a field
field :: Field r => r -> Parser r
field x = at_ x <$> readsMy 
  
  
-- | Parse zero or more fields
iter :: (r -> Parser r) -> r -> Parser r
iter step = rest
  where
    rest x = 
      (step x >>= rest)
        <|> return x
        
        
relpath :: RelPath r => Parser r
relpath = (self_ <$> readsMy) >>= iter field

localpath :: LocalPath r => Parser r
localpath = (local_ <$> readsMy) >>= iter field


-- | Parse a value extension
extend :: Extend r => r -> Parser (Group r) -> Parser r
extend r p = ext_ r <$> p

          
-- | Parse an expression observing operator precedence
orexpr :: Op r => Parser r -> Parser r
orexpr term =
  P.chainl1 (andexpr term) (binop_ <$> readOr)

andexpr :: Op r => Parser r -> Parser r
andexpr term =
  P.chainl1 (cmpexpr term) (binop_ <$> readAnd)
        
cmpexpr :: Op r => Parser r -> Parser r
cmpexpr term =
  do
    a <- addexpr term
    (do
       s <- op
       b <- addexpr term
       return (s a b))
      <|> return a
  where
    op = binop_ <$> (readGt <|> readLt <|> readEq <|> readNe <|> readGe <|> readLe)
      
addexpr :: Op r => Parser r -> Parser r
addexpr term =
  P.chainl1 (mulexpr term) (binop_ <$> (readAdd <|> readSub))

mulexpr :: Op r => Parser r -> Parser r
mulexpr term =
  P.chainl1 (powexpr term) (binop_ <$> (readProd <|> readDiv))

powexpr :: Op r => Parser r -> Parser r
powexpr term =
  P.chainl1 term (binop_ <$> readPow)
          
          
-- | Parse an unary operation
unop :: Op r => Parser r -> Parser r
unop term = unop_ <$> readsMy <*> term



syntax :: Syntax r => Parser r
syntax = orexpr term <?> "expression"
  where
    term =
      unop pathexpr   -- '!' ...
                      -- '-' ...
        <|> pathexpr  -- '"' ...
                      -- '(' ...
                      -- digit ...
                      -- '{' ...
                      -- '.' alpha ...
                      -- alpha ...
                      -- '@' ...
      
        
-- | Parse a chain of field accesses and extensions
pathexpr :: Syntax r => Parser r
pathexpr =
  first >>= rest
  where
    next :: Syntax r => r -> Parser r
    next x =
      (extend x group)
        <|> field x
    
    rest :: Syntax r => r -> Parser r
    rest = iter next
    
    first :: Syntax r => Parser r
    first =
      lit                         -- '"' ...
                                  -- digit ...
        <|> var                   -- '.' alpha ...
                                  -- alpha ...
                                  -- '@' ...
        <|> parens disambigTuple  -- '(' ...
        <|> block syntax          -- '{' ...
        <?> "value"
        
        
    group :: Syntax r => Parser (Group r)
    group = block syntax <|> tuple syntax
        
            
    -- | Handle a tricky parsing ambiguity between plain brackets and
    --   a singleton tuple, by requiring a trailing comma for the first
    --   statement of a tuple.
    --
    --   When an opening paren is encountered, we parse a rhs expression, and 
    --   check to see if the result can be interpreted as the beginning of a 
    --   tuple statement - only if the expression is a varpath - then we 
    --   disambiguate by looking next for an assignment `=` or a comma `,` 
    --   indicating a tuple expression. Otherwise we return rhs expression
    --   (and the calling function will then expect a closing paren).
    disambigTuple :: Syntax r => Parser r
    disambigTuple =
      (pubfirst                 -- '.' alpha
        <|> privfirst           -- alpha
        <|> pure (tup_ mempty))  -- ')'
      where
        privfirst = do
          p <- relpath
          (eqnext (getRelPath p)         -- '=' ...
            <|> sepnext (getRelPath p)   -- ',' ...
            <|> rest (getRelPath p))     -- ')' ...
          
        pubfirst = do
          p <- localpath
          (sepnext (getLocalPath p)        -- ',' ...
            <|> rest (getLocalPath p))     -- ')' ...
          
        eqnext p = tup_ <$> liftA2 mappend (assign p syntax) (tuple1 syntax)
        sepnext p = tup_ . mappend p <$> tuple1 syntax
        

-- | Wrap an ambiguously parsed path
--
-- For example
--     x.y.z
-- could be parsed, depending on what follows, as:
-- - a lhs of an assignment;
-- - a pun;
-- - a rhs path.
--
-- This wrapper allows the path to be established with different types
-- depending on the following parse.
newtype ARelPath = ARelPath { getRelPath :: forall a . RelPath a => a }
instance Self ARelPath where
  self_ k = ARelPath (self_ k)
  
instance Field ARelPath where
  ARelPath p `at_` k = ARelPath (p `at_` k)
  
instance RelPath ARelPath


newtype ALocalPath = ALocalPath { getLocalPath :: forall a . LocalPath a => a }
instance Local ALocalPath where
  local_ i = ALocalPath (local_ i)
  
instance Field ALocalPath where
  ALocalPath p `at_` k = ALocalPath (p `at_` k)
  
instance LocalPath ALocalPath
    
        
-- | Parse a tuple construction
tuple :: Tuple r => Parser (Member r) -> Parser r
tuple reads = (tup_ <$> parens (some <|> return mempty)) <?> "tuple"
  where
    some = liftA2 mappend (tupstmt reads) (tuple1 reads)
    
    
tuple1 :: (TupStmt s, Monoid s) => Parser (Rhs s) -> Parser s
tuple1 reads = commasep >> msepEndBy (tupstmt reads) commasep
    
    
-- | Parse a block construction
block :: Block r => Parser (Member r) -> Parser r
block reads =
  (block_ <$> braces (msepEndBy (recstmt reads) semicolonsep))
    <?> "block"


msepEndBy :: Monoid a => Parser a -> Parser b -> Parser a
msepEndBy p sep = msepEndBy p sep <|> return mempty

msepEndBy1 :: Monoid a => Parser a -> Parser b -> Parser a
msepEndBy1 p sep =
  do
    x <- p
    (do
      sep
      xs <- msepEndBy p sep
      return (x `mappend` xs))
      <|> return x


-- | Assignment
assign :: Let s => Lhs s -> Parser (Rhs s) -> Parser s
assign l reads = let_ l <$> (eqsep >> reads)

    
-- | Parse a statement of a tuple expression
tupstmt :: TupStmt s => Parser (Rhs s) -> Parser s
tupstmt reads =
  localpath       -- alpha ...
    <|> pubfirst  -- '.' alpha ...
  where
    pubfirst = do
      p <- relpath
      assign (getRelPath p) reads <|> return (getRelPath p)
    

-- | Parse a statement of a block expression
recstmt :: RecStmt s => Parser (Rhs s) -> Parser s
recstmt reads =
  pubfirst            -- '.' alpha ...
    <|> privfirst     -- alpha ...
    <|> ungroupfirst  -- '(' ...
    <?> "statement"
  where
    pubfirst = do
      p <- relpath
      (next (getRelPath p)          -- '('
                                    -- '='
        <|> return (getRelPath p))  -- ';'
                                    -- '}'
      
    privfirst = localpath >>= next
    ungroupfirst = ungroup >>= next
    
    next p = do
      p' <- extends p
      assign p' reads
      
extends :: Patt p => p -> Parser p
extends = iter (`extend` ungroup)
      
ungroup :: (Tuple p, Patt (Member p)) => Parser p
ungroup = tuple patt
    
patt :: Patt p => Parser p 
patt = (do
  p <- relpath    -- '.' alpha
    <|> ungroup   -- '('
  extends p)
    <?> "pattern"
    
    
-- | Parse a top-level sequence of statements
header :: Parser Import
header = readsMy <* ellipsissep


program :: Program r => Parser r
program = do
    m <- P.optionMaybe header
    x <- recstmt syntax
    (do
      semicolonsep
      xs <- msepEndBy (pure <$> recstmt syntax) semicolonsep
      (return . prog_ m) (option x (x<>) xs))
      <|> return (prog_ m x)
    <* P.eof

