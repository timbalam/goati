{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving, FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies #-}

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
  
  -- printer
  , Printer, showP, StmtPrinter, showGlobal
  )
  where
  
import My.Types.Syntax.Class
  ( Syntax, Expr, Defns
  , Self(..), Local(..), Extern(..), Lit(..)
  , Field(..), Extend(..), Block(..), Tuple(..)
  , Member, Sep(..), Splus(..)
  , Global(..)
  , Let(..), RecStmt, TupStmt
  , Path, LocalPath, RelPath, VarPath, Patt
  )
import My.Types.Syntax
  ( Ident(..), Key(..), Import(..)
  , Unop(..), Binop(..), prec
  )
import My.Parser
  ( readIdent, readKey, readImport
  , integer, comment, spaces, point, stringfragment, escapedchars, identpath
  , eqsep, semicolonsep, ellipsissep, commasep
  , braces, parens, staples
  , readOr, readAnd, readEq, readNe, readLt, readGt, readLe
  , readGe, readAdd, readSub, readProd, readDiv, readPow
  , readNeg, readNot
  , Parser, parse, ShowMy
  , showLitString, showLitText, showText, showIdent, showKey, showImport
  , showBinop, showUnop
  )
import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec ((<|>), (<?>), try)
import Numeric (readHex, readOct)
import Control.Applicative (liftA2)
import Data.Foldable (foldl')
import Data.Semigroup (Semigroup(..), option)


-- | Parsable text representation for syntax classes
data Printer = P PrecType ShowS

printP :: ShowS -> Printer
printP s = P Lit s

showP :: Printer -> ShowS
showP (P _ s) = s


data PrecType =
    Lit -- ^ literal, bracket, app
  | Unop Unop -- ^ Unary op
  | Binop Binop -- ^ Binary op
  
-- | Parsable text representation of statement with statement terminators and separators
data StmtPrinter = StmtP Count (String -> String -> ShowS)

stmtP :: ShowS -> StmtPrinter
stmtP s = StmtP One (\ e _ -> s . showString e)

instance Sep StmtPrinter where 
  StmtP n1 sep1 #: StmtP n2 sep2 =
    StmtP (n1 <> n2) (\ e s -> sep1 e s . showString s . sep2 e s)
  
instance Splus StmtPrinter where
  empty_ = StmtP mempty (\ _ _ -> id)

data Count = Zero | One | Many

instance Semigroup Count where
  Zero <> c = c
  c <> Zero = c
  One <> c = Many
  c <> One = Many
  Many <> Many = Many
  
instance Monoid Count where
  mempty = Zero
  mappend = (<>)
    
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
   
    
-- | Parser for valid decimal or floating point number
decfloat :: Lit r => Parser r
decfloat =
  prefixed
    <|> unprefixed
  where
    --prefixed :: Lit r => Parser r
    prefixed =
      do
        try (P.string "0d")
        int_ . read <$> integer P.digit
        
    unprefixed =
      do
        xs <- integer P.digit
        fracnext xs                       -- int frac
                                          -- int frac exp
          <|> expnext xs                  -- int exp
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
        
        
instance Lit Printer where
  int_ = printP . shows
  num_ = printP . shows
  str_ t = printP (showChar '"' . showLitText t . showChar '"')
  
  unop_ o (P prec s) =
    P (Unop o) (showUnop o . showParen (test prec) s)
    where
      test (Binop _) = True
      test _ = False
      
  binop_ o (P prec1 s1) (P prec2 s2) =
    P (Binop o)(showParen (test prec1) s1 . showChar ' '
      . showBinop o . showChar ' ' . showParen (test prec2) s2)
    where
      test (Binop p) = prec o p
      test _ = False


-- | Parse a double-quote wrapped string literal
string :: Expr r => Parser r
string =
  str_ . T.pack <$> stringfragment <?> "string literal"
  
  
-- | Parse a field
field :: Field r => Compound r -> Parser r
field x = (x #.) <$> readKey

instance Field Printer where
  type Compound Printer = Printer
  P prec s #. k = printP (showParen (test prec) s . showKey k) where
    test Lit = False
    test _ = True
    
instance Path Printer
  
    
  
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
relpath :: (Self a, Field a, Self (Compound a), Path (Compound a)) => Parser a
relpath = (self_ <$> readKey) >>= fmap getRelPath . iter field

localpath :: (Local a, Field a, Local (Compound a), Path (Compound a)) => Parser a
localpath = (local_ <$> readIdent) >>= fmap getLocalPath . iter field

-- | These newtype wrappers for the class dictionaries allow the path to be instantiated
-- with type 'a' or 'Compound a' as needed 
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

instance Extend Printer where
  type Ext Printer = Printer
  P prec1 s1 # P prec2 s2 =
    printP (showParen (test prec1) s1 . showParen (test prec2) s2) 
    where
      test Lit = False
      test _ = True

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

instance Self Printer where
  self_ = printP . showKey
  
instance Local Printer where
  local_ = printP . showIdent
  
instance Extern Printer where
  use_ = printP . showImport
  
instance RelPath Printer
instance VarPath Printer

        
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
        <|> pure (tup_ empty_))  -- ')'
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
        eqnext p = tup_ <$> liftA2 (#:) (assign p syntax) (tuple1 syntax)
        
        sepnext :: Syntax r => Tup r -> Parser r
        sepnext p = tup_ . (p #:) <$> tuple1 syntax

    
group :: Syntax r => Parser (Ext r)
group = block syntax <|> tuple syntax

type instance Member Printer = Printer

instance Tuple Printer where
  type Tup Printer = StmtPrinter
  
  tup_ (StmtP One sep) = printP (showString "(" . sep "" ", " . showString ",)")
  tup_ (StmtP _ sep) = printP (showString "(" . sep "" ", " . showString ")")
      
instance Block Printer where
  type Rec Printer = StmtPrinter
  
  block_ (StmtP _ sep) = printP (showString "{" . sep "" "; " . showString "}")
  
instance Patt Printer
instance Defns Printer
instance Expr Printer
instance Syntax Printer
  
instance Self StmtPrinter where
  self_ k = stmtP (showKey k)
  
instance Local StmtPrinter where
  local_ i = stmtP (showIdent i)
  
instance Field StmtPrinter where
  type Compound StmtPrinter = Printer
  p #. k = (stmtP . showP) (p #. k)
  
instance RelPath StmtPrinter
instance VarPath StmtPrinter

        
-- | Parse a tuple construction
tuple :: Tuple r => Parser (Member r) -> Parser r
tuple p = (tup_ <$> parens (some <|> return empty_)) <?> "tuple"
  where
    some = liftA2 (#:) (tupstmt p) (tuple1 p)
    
    
tuple1 :: (TupStmt s, Splus s) => Parser (Rhs s) -> Parser s
tuple1 p = commasep >> asepEndBy (tupstmt p) commasep
    
    
-- | Parse a block construction
block :: Block r => Parser (Member r) -> Parser r
block p =
  (block_ <$> braces (asepEndBy (recstmt p) semicolonsep))
    <?> "block"


asepEndBy :: Splus s => Parser s -> Parser b -> Parser s
asepEndBy p sep = asepEndBy1 p sep <|> return empty_

asepEndBy1 :: Splus s => Parser s -> Parser b -> Parser s
asepEndBy1 p sep =
  do
    x <- p
    (do
      sep
      xs <- asepEndBy p sep
      return (x #: xs))
      <|> return x


-- | Assignment
assign :: Let s => Lhs s -> Parser (Rhs s) -> Parser s
assign l p = (l #=) <$> (eqsep >> p)

    
-- | Parse a statement of a tuple expression
tupstmt :: TupStmt s => Parser (Rhs s) -> Parser s
tupstmt p =
  (getLocalPath <$> localpath)  -- alpha ...
    <|> pubfirst                -- '.' alpha ...
  where
    pubfirst = do
      ARelPath apath <- relpath
      assign apath p <|> return apath
      
instance Let Printer where
  type Lhs Printer = Printer
  type Rhs Printer = Printer
  p1 #= p2 = printP (showP p1 . showString " = " . showP p2)
      
instance Let StmtPrinter where
  type Lhs StmtPrinter = Printer
  type Rhs StmtPrinter = Printer
  p1 #= p2 = (stmtP . showP) (p1 #= p2)
  
instance TupStmt StmtPrinter
  
instance RecStmt StmtPrinter
    

-- | Parse a statement of a block expression
recstmt :: RecStmt s => Parser (Rhs s) -> Parser s
recstmt p =
  pubfirst            -- '.' alpha ...
    <|> privfirst     -- alpha ...
    <|> ungroupfirst  -- '(' ...
    <?> "statement"
  where
    pubfirst = do
      ARelPath apath <- relpath
      (next apath           -- '('
                            -- '='
        <|> return apath)   -- ';'
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
  p <- relpath      -- '.' alpha
    <|> localpath   -- alpha
    <|> ungroup     -- '('
  extends p)
    <?> "pattern"
    
    
-- | Parse a top-level sequence of statements
header :: Parser Import
header = readImport <* ellipsissep

-- | Wrapper to lift 'Sep a => a' to 'Splus'
newtype OptionS a = OptionS (Maybe a)
  deriving (Functor, Applicative)

optionS :: b -> (a -> b) -> OptionS a -> b
optionS b f (OptionS m) = maybe b f m

instance Sep a => Sep (OptionS a) where
  OptionS a #: OptionS b = OptionS (liftA2 (#:) a b)
  
instance Sep a => Splus (OptionS a) where
  empty_ = OptionS Nothing
  

program :: (RecStmt s, Sep s, Syntax (Rhs s)) => Parser s
program = do 
  x <- recstmt syntax
  (do
    semicolonsep
    xs <- asepEndBy (pure <$> recstmt syntax) semicolonsep
    return (optionS x (x#:) xs))
    <|> return x

global :: (Global s, Body s ~ s)
 => Parser s
--global :: Global r, Member r ~ f a, Body r ~ s) => Parser r
global = do
  m <- P.optionMaybe header
  AProgram xs <- program -- Body s
  return (maybe xs (#... xs) m) 
  <* P.eof

showGlobal :: StmtPrinter -> ShowS
showGlobal (StmtP _ sep) = sep ";" "\nn"

type instance Member StmtPrinter = Printer

instance Global StmtPrinter where
  type Body StmtPrinter = StmtPrinter
  
  i #... b = StmtP One (\ _ _ -> showImport i . showString "...") #: b
  
 
newtype AProgram l r = AProgram {
    getProgram :: forall s. (RecStmt s, Lhs s ~ l, Rhs s ~ r, Sep s) => s
  }
  
instance Self (AProgram l r) where
  self_ i = AProgram (self_ i)
  
instance Field (AProgram l r) where
  type Compound (AProgram l r) = ARelPath
  
  ARelPath p #. k = AProgram (p #. k)

instance RelPath (AProgram l r)
  
instance (Patt l, Syntax r) => Let (AProgram l r) where
  type Lhs (AProgram l r) = l
  type Rhs (AProgram l r) = r
  
  l #= r = AProgram (l #= r)

instance (Patt l, Syntax r) => RecStmt (AProgram l r)

instance Sep (AProgram l r) where
  AProgram a #: AProgram b = AProgram (a #: b)

