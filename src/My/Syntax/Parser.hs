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
  , braces, parens, staples
  , Parser, parse, ShowMy
  , showLitString, showLitText, showText, showIdent, showKey, showImport
  , showBinop, showUnop
  )
import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec ((<|>), (<?>), try)
import Numeric (readHex, readOct)
import Control.Applicative (liftA2, (<**>))
import My.Util ((<&>))
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
  
-- | Parsable text representation of statement with statement separators and whitespace
data StmtPrinter = StmtP Count (String -> String -> ShowS)

stmtP :: ShowS -> StmtPrinter
stmtP s = StmtP One (\ _ _ -> s)

instance Sep StmtPrinter where 
  StmtP n1 ss1 #: StmtP n2 ss2 =
    StmtP (n1 <> n2) (\ w s -> ss1 s w . showString s . showString w . ss2 s w)
  
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
        
        
-- | Parse a double-quote wrapped string literal
string :: Expr r => Parser r
string =
  str_ . T.pack <$> stringfragment <?> "string literal"
        
        
-- | Parse binary operators
readOr, readAnd, readEq, readNe, readLt, readGt, readLe, readGe, readAdd,
  readSub, readProd, readDiv, readPow  :: Lit r => Parser (r -> r -> r)
readOr = P.char '|' >> spaces >> return (binop_ Or)
readAnd = P.char '&' >> spaces >> return (binop_ And)
readEq = try (P.string "==") >> spaces >> return (binop_ Eq)
readNe = try (P.string "!=") >> spaces >> return (binop_ Ne)
readLt = try (P.char '<' >> P.notFollowedBy (P.char '=')) >> spaces >> return (binop_ Lt)
readGt = try (P.char '>' >> P.notFollowedBy (P.char '=')) >> spaces >> return (binop_ Gt)
readLe = try (P.string "<=") >> spaces >> return (binop_ Le)
readGe = try (P.string ">=") >> spaces >> return (binop_ Ge)
readAdd = P.char '+' >> spaces >> return (binop_ Add)
readSub = P.char '-' >> spaces >> return (binop_ Sub)
readProd = P.char '*' >> spaces >> return (binop_ Prod)
readDiv = P.char '/' >> spaces >> return (binop_ Div)
readPow = P.char '^' >> spaces >> return (binop_ Pow)


-- | Parse unary operators
readNeg, readNot :: Lit r => Parser (r -> r)
readNeg = P.char '-' >> spaces >> return (unop_ Neg)
readNot = P.char '!' >> spaces >> return (unop_ Not)
        
        
-- | Printer for literal syntax
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
    P (Binop o) (showParen (test prec1) s1 . showChar ' '
      . showBinop o . showChar ' ' . showParen (test prec2) s2)
    where
      test (Binop p) = prec o p
      test _ = False
  
  
-- | Parse a local name
local :: Local r => Parser r
local = local_ <$> readIdent


-- | Parse a public name
self :: Self r => Parser r
self = self_ <$> readKey


-- | Parse an external name
use :: Extern r => Parser r
use = use_ <$> readImport
  
  
-- | Parse a field
field :: Field r => Parser (Compound r -> r)
field = flip (#.) <$> readKey


instance Self Printer where
  self_ = printP . showKey
  
instance Local Printer where
  local_ = printP . showIdent
  
instance Extern Printer where
  use_ = printP . showImport

instance Field Printer where
  type Compound Printer = Printer
  P prec s #. k = printP (showParen (test prec) s . showKey k) where
    test Lit = False
    test _ = True
    
instance Path Printer
instance LocalPath Printer
instance RelPath Printer
instance VarPath Printer

  
instance Self StmtPrinter where
  self_ k = stmtP (showKey k)
  
instance Local StmtPrinter where
  local_ i = stmtP (showIdent i)
  
instance Field StmtPrinter where
  type Compound StmtPrinter = Printer
  p #. k = (stmtP . showP) (p #. k)
  
instance RelPath StmtPrinter
instance VarPath StmtPrinter


-- | Parse a value extension
extend :: Extend r => Parser (r -> Ext r -> r)
extend = pure (#)

instance Extend Printer where
  type Ext Printer = Printer
  P prec1 s1 # P prec2 s2 =
    printP (showParen (test prec1) s1 . showParen (test prec2) s2) 
    where
      test Lit = False
      test _ = True
  
  
-- | Parse statement equals definition
assign :: Let r => Parser (Lhs r -> Rhs r -> r)
assign = P.char '=' >> spaces >> return (#=)
            
    
-- | Parse statement separators
recstmtsep :: (Sep r, RecStmt r) => Parser (r -> Maybe r -> r)
recstmtsep =
  P.char ';' >> spaces >> return (maybe <*> (#:))
  
  
tupstmtsep :: (Sep r, TupStmt r) => Parser (r -> Maybe r -> r)
tupstmtsep =
  P.char ',' >> spaces >> return (maybe <*> (#:))
  
  
global :: Global r => Parser (Import -> Body r -> r)
global =
  try (P.string "..." <* P.notFollowedBy (P.char '.')) >> spaces >> return (#...)
  
    
  
-- | Parse zero or more nested modifications
iter :: Parser (r -> r) -> Parser (r -> r)
iter step = rest
  where
    rest = liftA2 (flip (.)) step rest <|> return id
          

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
relpath = getRelPath <$> (self <**> iter field)

localpath :: (Local a, Field a, Local (Compound a), Path (Compound a)) => Parser a
localpath = getLocalPath <$> (local <**> iter field)

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


-- | Parse an expression observing operator precedence
orexpr :: Syntax r => Parser r
orexpr =
  P.chainl1 andexpr readOr

andexpr :: Syntax r => Parser r
andexpr =
  P.chainl1 cmpexpr readAnd
        
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
    op = readGt <|> readLt <|> readEq <|> readNe <|> readGe <|> readLe
      
addexpr :: Syntax r => Parser r
addexpr =
  P.chainl1 mulexpr (readAdd <|> readSub)

mulexpr :: Syntax r => Parser r
mulexpr =
  P.chainl1 powexpr (readProd <|> readDiv)

powexpr :: Syntax r => Parser r
powexpr =
  P.chainl1 term readPow
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
unop = (readNot <|> readNeg) <*> pathexpr


syntax :: Syntax r => Parser r
syntax = orexpr <?> "expression"

        
-- | Parse a chain of field accesses and extensions
pathexpr :: Syntax r => Parser r
pathexpr =
  first <**> rest
  where
    step :: Syntax r => Parser (r -> r)
    step =
      liftA2 flip extend group  -- '(' ...
                                -- '{' ...
        <|> field               -- '.' ...
    
    rest :: Syntax r => Parser (r -> r)
    rest = iter step
    
    first :: Syntax r => Parser r
    first =
      string                      -- '"' ...
        <|> number                -- digit ...
        <|> local                 -- alpha
        <|> self                  -- '.' alpha
        <|> use                   -- '@'
        <|> parens disambigTuple  -- '(' ...
        <|> block syntax          -- '{' ...
        <?> "value"
        
            
    -- | Handle a tricky parsing ambiguity between plain brackets and
    -- a singleton tuple, by requiring a trailing comma for the first
    -- statement of a tuple.
    --
    -- When an opening paren is encountered, we parse a rhs expression, and 
    -- check to see if the result can be interpreted as the beginning of a 
    -- tuple statement - only if the expression is a varpath - then we 
    -- disambiguate by looking next for an assignment `=` or a comma `,` 
    -- indicating a tuple expression. Otherwise we return rhs expression
    -- (and the calling function will then expect a closing paren).
    disambigTuple :: Syntax r => Parser r
    disambigTuple =
      (pubfirst                 -- '.' alpha
        <|> privfirst           -- alpha
        <|> pure (tup_ empty_))  -- ')'
      where
        privfirst :: Syntax r => Parser r
        privfirst = do
          ARelPath p <- relpath
          (tup_ <$> (liftA2 ($ p) assign syntax <**> tup1)  -- '=' ...
            <|> tup_ . ($ p) <$> tup1                         -- ',' ...
            <|> ($ p) <$> rest)                               -- ')' ...
          
        pubfirst = do
          ALocalPath p <- localpath
          (tup_ . ($ p) <$> tup1   -- ',' ...
            <|> ($ p) <$> rest)        -- ')' ...
        
        tup1 :: (TupStmt r, Sep r, Syntax (Rhs r)) => Parser (r -> r)
        tup1 = sep1 (tupstmt syntax) tupstmtsep
        
    
group :: Syntax r => Parser (Ext r)
group = block syntax <|> tuple syntax

        
-- | Parse a tuple construction
tuple :: Tuple r => Parser (Member r) -> Parser r
tuple p = tup_ <$> parens tup <?> "tuple" where
  tup = P.option empty_ (tupstmt p <**> sep1 (tupstmt p) tupstmtsep)
    
    
-- | Parse a block construction
block :: Block r => Parser (Member r) -> Parser r
block p = block_ <$> braces rec <?> "block" where
  rec = P.option empty_ (sep (recstmt p) recstmtsep)


sep :: Parser s -> Parser (s -> Maybe s -> s) -> Parser s
sep p s = p <**> (sep1 p s <|> return id)
    
    
-- | Parse a trailing separator and optionally more statements
sep1 :: Parser s -> Parser (s -> Maybe s -> s) -> Parser (s -> s)
sep1 p s = liftA2 flip s (P.optionMaybe (sep p s))

type instance Member Printer = Printer

instance Tuple Printer where
  type Tup Printer = StmtPrinter
  
  tup_ (StmtP One ss) = printP (showString "(" . ss "," " " . showString ",)")
  tup_ (StmtP _ ss) = printP (showString "(" . ss "," " " . showString ")")
      
instance Block Printer where
  type Rec Printer = StmtPrinter
  
  block_ (StmtP _ ss) = printP (showString "{" . ss ";" " " . showString "}")
  
instance Patt Printer
instance Defns Printer
instance Expr Printer
instance Syntax Printer

    
-- | Parse a statement of a tuple expression
tupstmt :: TupStmt s => Parser (Rhs s) -> Parser s
tupstmt p =
  localpath         -- alpha ...
    <|> pubfirst    -- '.' alpha ...
  where
    pubfirst = do
      ARelPath apath <- relpath
      (liftA2 ($ apath) assign p) <|> return apath
    

-- | Parse a statement of a block expression
recstmt :: RecStmt s => Parser (Rhs s) -> Parser s
recstmt p =
  pubfirst          -- '.' alpha ...
    <|> pattfirst   -- alpha ...
                    -- '(' ...
    <?> "statement"
  where
    pubfirst = do
      ARelPath apath <- relpath
      (($ apath) <$> pattrest <**> assign <*> p   -- '(' ...
                                                  -- '=' ...
        <|> return apath)
      
    pattfirst =
      (localpath      -- alpha ...
        <|> ungroup)  -- '(' ...
        <**> pattrest <**> assign <*> p
      
    pattrest :: Patt p => Parser (p -> p)
    pattrest = iter (liftA2 flip extend ungroup)
          
    ungroup :: (Tuple p, Patt (Member p)) => Parser p
    ungroup = tuple patt
        
    patt :: Patt p => Parser p 
    patt =
      (relpath          -- '.' alpha
        <|> localpath   -- alpha
        <|> ungroup)    -- '('
        <**> pattrest
        <?> "pattern"
      
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
    
    
-- | Parse a top-level sequence of statements
header :: Global r => Parser (Body r -> r)
header = readImport <**> global
  
body :: (RecStmt s, Sep s, Syntax (Rhs s)) => Parser s
body = sep (recstmt syntax) recstmtsep

program :: (Global s, Body s ~ s)
 => Parser s
program = do
  mf <- P.optionMaybe header
  ABody xs <- body
  return (maybe xs ($ xs) mf) 
  <* P.eof

  
showGlobal :: StmtPrinter -> ShowS
showGlobal (StmtP _ ss) = ss ";" "\n\n"

type instance Member StmtPrinter = Printer

instance Global StmtPrinter where
  type Body StmtPrinter = StmtPrinter
  
  i #... StmtP n ss = StmtP (One <> n)
    (\ s w -> showImport i . showString "..." . showString w . ss s w)
  
 
newtype ABody l r = ABody {
    getProgram :: forall s. (RecStmt s, Lhs s ~ l, Rhs s ~ r, Sep s) => s
  }
  
instance Self (ABody l r) where
  self_ i = ABody (self_ i)
  
instance Field (ABody l r) where
  type Compound (ABody l r) = ARelPath
  ARelPath p #. k = ABody (p #. k)

instance RelPath (ABody l r)
  
instance (Patt l, Syntax r) => Let (ABody l r) where
  type Lhs (ABody l r) = l
  type Rhs (ABody l r) = r
  l #= r = ABody (l #= r)

instance (Patt l, Syntax r) => RecStmt (ABody l r)

instance Sep (ABody l r) where
  ABody a #: ABody b = ABody (a #: b)

