{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies #-}

-- | Parsers for my syntax types

module My.Syntax.Parser
  ( decfloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , pathexpr
  , syntax
  , program
  , global
  , Parser, parse
  )
  where
  
import My.Types.Syntax.Class
  ( Syntax, Self(..), Local(..), Extern(..), Expr(..)
  , Field(..), Extend(..), Block(..), Tuple(..), Member
  , Global(..)
  , Let(..), RecStmt, TupStmt
  , Path, LocalPath, RelPath, VarPath, Patt
  , Self1(..), Field1(..), RelPath1, S(..)
  )
import My.Types.Syntax
  ( Ident(..), Key(..), Import(..)
  , Unop(..), Binop(..)
  )
import My.Parser
  ( readIdent, readKey, readImport
  , integer, comment, spaces, point, stringfragment, escapedchars, identpath
  , eqsep, semicolonsep, ellipsissep, commasep
  , braces, parens, staples
  , readOr, readAnd, readEq, readNe, readLt, readGt, readLe
  , readGe, readAdd, readSub, readProd, readDiv, readPow
  , readNeg, readNot
  , Parser, parse
  )
import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec ((<|>), (<?>), try)
import Numeric (readHex, readOct)
import Control.Applicative (liftA2)
import Data.Foldable (foldl')
import Data.Semigroup (Semigroup(..), option)
import Data.Functor.Alt (Alt(..))
import Data.Functor.Plus (Plus(..))
     
    
-- | Parse any valid numeric literal
number :: Expr r => Parser r
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number literal")
    <* spaces
    
    
-- | Parse a valid binary number
binary :: Expr r => Parser r
binary =
  do
    try (P.string "0b")
    int_ . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: Expr r => Parser r
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . int_ . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: Expr r => Parser r
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . int_ . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
   
    
-- | Parser for valid decimal or floating point number
decfloat :: Expr r => Parser r
decfloat =
  prefixed
    <|> unprefixed
  where
    prefixed :: Expr r => Parser r
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
string :: Expr r => Parser r
string =
  str_ . T.pack <$> stringfragment <?> "string literal"
  
  
-- | Parse a field
field :: Field r => Compound r -> Parser r
field x = (x #.) <$> readKey
  
  
-- | Parse zero or more nested fields
iter :: (r -> Parser r) -> r -> Parser r
iter step = rest
  where
    rest x = 
      (step x >>= rest)
        <|> return x
          

-- | Ambiguous path parsing
--
-- For example
--     x.y.z
-- could be parsed, depending on what follows, as:
-- - a lhs of an assignment;
-- - a pun;
-- - a rhs path.
--
-- We can wrap the path so that it can be established with different types
-- depending on the following parse.
relpath :: RelPath p => Parser p
relpath = (self_ <$> readKey) >>= fmap getRelPath . iter field

localpath :: LocalPath p => Parser p
localpath = (local_ <$> readIdent) >>= fmap getLocalPath . iter field

newtype ARelPath = ARelPath
  { getRelPath
    :: forall a . (Self a, Field a, Self (Compound a), Path (Compound a)) => a
  }
  
newtype ALocalPath = ALocalPath
  { getLocalPath
    :: forall a . (Local a, Field a, Local (Compound a), Path (Compound a)) => a
  }
  
instance Self ARelPath where
  self_ k = ARelPath (self_ k)
  
instance Field ARelPath where
  type Compound ARelPath = ARelPath
  
  ARelPath p #. k = ARelPath (p #. k) 
  
instance Path ARelPath
  
instance RelPath ARelPath

instance Local ALocalPath where
  local_ i = ALocalPath (local_ i)
  
instance Field ALocalPath where
  type Compound ALocalPath = ALocalPath
  
  ALocalPath p #. k = ALocalPath (p #. k)
  
instance Path ALocalPath

instance LocalPath ALocalPath


-- | Parse a value extension
extend :: Extend r => r -> Parser (Ext r) -> Parser r
extend r p = (r #) <$> p

-- | Parse an expression observing operator precedence
orexpr :: Syntax r => Parser r
orexpr =
  P.chainl1 andexpr (binop_ <$> readOr)

andexpr :: Syntax r => Parser r
andexpr =
  P.chainl1 cmpexpr (binop_ <$> readAnd)
        
cmpexpr :: Syntax r => Parser r
cmpexpr =
  do
    a <- addexpr
    (do
       s <- op
       b <- addexpr
       return (s a b))
      <|> return a
  where
    op = binop_ <$> (readGt <|> readLt <|> readEq <|> readNe <|> readGe <|> readLe)
      
addexpr :: Syntax r => Parser r
addexpr =
  P.chainl1 mulexpr (binop_ <$> (readAdd <|> readSub))

mulexpr :: Syntax r => Parser r
mulexpr =
  P.chainl1 powexpr (binop_ <$> (readProd <|> readDiv))

powexpr :: Syntax r => Parser r
powexpr =
  P.chainl1 term (binop_ <$> readPow)
  where
    term =
      unop            -- '!' ...
                      -- '-' ...
        <|> pathexpr  -- '"' ...
                      -- '(' ...
                      -- digit ...
                      -- '{' ...
                      -- '.' alpha ...
                      -- alpha ...
                      -- '@' ...
          
          
-- | Parse an unary operation
unop :: Syntax r => Parser r
unop = unop_ <$> (readNot <|> readNeg) <*> pathexpr


syntax :: Syntax r => Parser r
syntax = orexpr <?> "expression"
      
        
-- | Parse a chain of field accesses and extensions
pathexpr :: Syntax r => Parser r
pathexpr =
  first >>= rest
  where
    next :: Syntax r => r -> Parser r
    next x =
      (x `extend` group)
        <|> field x
    
    rest :: Syntax r => r -> Parser r
    rest = iter next
    
    first :: Syntax r => Parser r
    first =
      string                        -- '"' ...
        <|> number                  -- digit ...
        <|> (local_ <$> readIdent)  -- alpha
        <|> (self_ <$> readKey)     -- '.' alpha
        <|> (use_ <$> readImport)   -- '@'
        <|> parens disambigTuple  -- '(' ...
        <|> block syntax          -- '{' ...
        <?> "value"
        
            
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
        <|> pure (tup_ zero))  -- ')'
      where
        privfirst :: Syntax r => Parser r
        privfirst = do
          ARelPath p <- relpath
          (eqnext p         -- '=' ...
            <|> sepnext p   -- ',' ...
            <|> rest p)     -- ')' ...
          
        pubfirst = do
          ALocalPath p <- localpath
          (sepnext p        -- ',' ...
            <|> rest p)     -- ')' ...
        
        eqnext :: Syntax r => Lhs (Tup r) -> Parser r
        eqnext p = tup_ . S <$> liftA2 (<!>) (assign p syntax) (tuple1 syntax)
        
        sepnext :: Syntax r => S (Tup r) r -> Parser r
        sepnext p = tup_ . (p <!>) . S <$> tuple1 syntax

    
group :: Syntax r => Parser (Ext r)
group = block syntax <|> tuple syntax
    
        
-- | Parse a tuple construction
tuple :: Tuple r => Parser (Member r) -> Parser r
tuple p = (tup_ . S <$> parens (some <|> return zero)) <?> "tuple"
  where
    some = liftA2 (<!>) (tupstmt p) (tuple1 p)
    
    
tuple1 :: (TupStmt s, Plus s) => Parser a -> Parser (s a)
tuple1 p = commasep >> asepEndBy (tupstmt p) commasep
    
    
-- | Parse a block construction
block :: Block r => Parser (Member r) -> Parser r
block p =
  (block_ . S <$> braces (asepEndBy (recstmt p) semicolonsep))
    <?> "block"


asepEndBy :: Plus s => Parser (s a) -> Parser b -> Parser (s a)
asepEndBy p sep = asepEndBy p sep <|> return zero

asepEndBy1 :: Plus s => Parser (s a) -> Parser b -> Parser (s a)
asepEndBy1 p sep =
  do
    x <- p
    (do
      sep
      xs <- asepEndBy p sep
      return (x <!> xs))
      <|> return x


-- | Assignment
assign :: Let s => Lhs s -> Parser a -> Parser (s a)
assign l p = (l #=) <$> (eqsep >> p)

    
-- | Parse a statement of a tuple expression
tupstmt :: TupStmt s => Parser a -> Parser (s a)
tupstmt p =
  (getS . getLocalPath <$> localpath)   -- alpha ...
    <|> pubfirst                        -- '.' alpha ...
  where
    pubfirst = do
      ARelPath apath <- relpath
      assign apath p <|> return (getS apath)
    

-- | Parse a statement of a block expression
recstmt :: RecStmt s => Parser a -> Parser (s a)
recstmt p =
  pubfirst            -- '.' alpha ...
    <|> privfirst     -- alpha ...
    <|> ungroupfirst  -- '(' ...
    <?> "statement"
  where
    pubfirst = do
      ARelPath apath <- relpath
      (next apath                 -- '('
                                  -- '='
        <|> return (getS apath))  -- ';'
                                  -- '}'
      
    privfirst = localpath >>= next . getLocalPath
    ungroupfirst = ungroup >>= next
    
    next patt = extends patt >>= (`assign` p)
      
      
extends :: Patt p => p -> Parser p
extends = iter (`extend` ungroup)
      
ungroup :: (Tuple p, Patt (Member p)) => Parser p
ungroup = tuple patt
    
patt :: Patt p => Parser p 
patt = (do
  p <- (getRelPath <$> relpath)  -- '.' alpha
    <|> tuple ungroup            -- '('
  extends p)
    <?> "pattern"
    
    
-- | Parse a top-level sequence of statements
header :: Parser Import
header = readImport <* ellipsissep

program :: (RecStmt s, Alt s, Syntax a) => Parser (s a)
program = do 
  x <- recstmt syntax
  (do
    semicolonsep
    xs <- asepEndBy (pure <$> recstmt syntax) semicolonsep
    return (option x (x<!>) xs))
    <|> return x

global :: (Applicative f, Global (f (s a)), Body (f (s a)) ~ s, Member (f (s a)) ~  f a)
 => Parser (f (s a))
--global :: Global r, a ~ Member r, RecStmt (Body r), Alt (Body r)) => Parser r
global = do
  m <- P.optionMaybe header
  AProgram xs <- program
  return (maybe (sequenceA xs) (#... S xs) m) 
  <* P.eof
 
 
newtype AProgram l a = AProgram (forall s. (RecStmt s, Lhs s ~ l, Alt s) => s a)
  deriving Functor

  
instance Self1 (AProgram l) where
  self1_ i = AProgram (self1_ i)
  
instance Field1 (AProgram l) where
  type Compound1 (AProgram l) = ARelPath
  
  ARelPath p `at1_` k = AProgram (p `at1_` k)

instance RelPath1 (AProgram l)
  
instance Patt l => Let (AProgram l) where
  type Lhs (AProgram l) = l
  
  l #= r = AProgram (l #= r)

instance Patt l => RecStmt (AProgram l)

instance Alt (AProgram l) where
  AProgram a <!> AProgram b = AProgram (a <!> b)

