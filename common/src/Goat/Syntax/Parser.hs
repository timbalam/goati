{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving, FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies, ScopedTypeVariables #-}

-- | This module implements parsers for the various forms of Goat syntax described by the typeclass-encoding in 'Goat.Types.Syntax.Class'.
-- Additionally, the module implements a (not-very) pretty-printer 'Printer'.
module Goat.Syntax.Parser
  ( decfloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , pathexpr
  , syntax
  , program'
  , Parser, parse
  , program
  --, NonEmpty(..)
  
  -- printer
  , Printer, showP, showProgram', showIdent
  )
  where
  
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident (showIdent, parseIdent)
import Goat.Syntax.Symbol ( Symbol(..), showSymbol, parseSymbol )
import Goat.Syntax.Field (parseField)
import Goat.Syntax.Binop (parseArith, parseCmp, parseLogic)
import Goat.Syntax.Unop (parseUn)
import Goat.Syntax.Class hiding (Unop(..), Binop(..), prec)
import qualified Goat.Syntax.Class as S (Unop(..), Binop(..), prec)
import Goat.Util ((<&>))
import Control.Applicative (liftA2, (<**>), liftA3)
import Data.Char (showLitChar)
--import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import Data.Ratio ((%))
import Data.Foldable (foldl')
import Data.Semigroup (Semigroup(..), option)
import Data.Monoid(Endo(..))
import Data.String (IsString(..))
import qualified Text.Parsec as P
import Text.Parsec ((<|>), (<?>), try, parse)
import Text.Parsec.Text  (Parser)
import Text.Read (readMaybe)
import Numeric (readHex, readOct)


type Binop = Symbol


-- | Parsable text representation for syntax classes
data Printer = P PrecType ShowS

printP :: ShowS -> Printer
printP s = P Lit s

showP :: Printer -> ShowS
showP (P _ s) = s


data PrecType =
    Lit -- ^ literal, bracket, app
  | Unop S.Unop
  | Binop S.Binop  -- ^ Binary op
  | Use -- ^ Use statement
  | Esc -- ^ Escaped expression
  
  
-- | Parse a sequence of underscore spaced digits
integer :: Parser a -> Parser [a]
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
  
  
-- | Parse a single decimal point / field accessor
--   (requires disambiguation from extension dots)
point :: Parser ()
point = parseSymbol Dot *> return ()


-- | Parse a double-quote wrapped string literal
stringfragment :: Parser String
stringfragment =
  P.between
    (P.char '"')
    (P.char '"' >> spaces)
    (P.many (P.noneOf "\"\\" <|> escapedchars))

    
-- | Parse an escaped character
escapedchars :: Parser Char
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
          
          
ident :: Parser Ident
ident = parseIdent
    
    
-- | Parse any valid numeric literal
number :: (Fractional r, Num r) => Parser r
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number literal")
    <* spaces
    
    
-- | Parse a valid binary number
binary :: Num r => Parser r
binary =
  do
    try (P.string "0b")
    fromInteger . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: Num r => Parser r
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . fromInteger . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: Num r => Parser r
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . fromInteger . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
      
      
-- | Parse a digit
digit :: Parser Int
digit = do
  d <- P.digit
  return (read [d])
  

-- | Parse a list of digits
digits :: Parser [Int]
digits = integer digit

  
-- | Parser for valid decimal or floating point number
decfloat :: (Num r, Fractional r) => Parser r
decfloat =
  prefixed
    <|> unprefixed
  where
    -- based on code from
    -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#val
    val :: Integer -> [Int] -> Integer
    val base = foldl' go 0
      where
        go r d = r * base + fromIntegral d
        
    -- based on code from
    -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#fracExp
    frac :: Integer -> Integer -> [Int] -> Rational
    frac exp mant fs = if exp' < 0
      then mant' % (10 ^ (-exp'))
      else  fromInteger (mant' * 10^exp')
      where
        (exp', mant') = foldl' go (exp, mant) fs
        go (e, r) d = (e-1, r * 10 + fromIntegral d)
    
    --prefixed :: Lit r => Parser r
    prefixed =
      do
        try (P.string "0d")
        ds <- digits
        (return . fromInteger) (val 10 ds)
        
    unprefixed =
      do
        P.optional (P.char '+')
        ds <- digits
        let i = val 10 ds
        fracnext i                        -- int frac
                                          -- int frac exp
          <|> expnext i []                -- int exp
          <|> return (fromInteger i)      -- int
          
    fracnext i =
      do 
        point
        mf <- P.optionMaybe digits
        case mf of
          Nothing ->
            (return . fromRational) (fromInteger i)     -- frac
            
          Just f ->
            expnext i f                                 -- frac exp
              <|> (return . fromRational) (frac 0 i f)  -- frac
          
    expnext i f =
      do 
        P.oneOf "eE"
        sgn <- P.option [] (P.oneOf "+-" >>= return . pure)
        ds <- digits
        let
          exp = case sgn of
            "-" -> -(val 0 ds)
            _ -> val 0 ds
        (return . fromRational) (frac exp i f)
        
        
-- | Parse a double-quote wrapped string literal
string :: IsString r => Parser r
string =
  fromString <$> stringfragment <?> "string literal"
        
        
-- | Parse binary operators
readOr, readAnd, readEq, readNe, readLt, readGt, readLe, readGe, readAdd,
  readSub, readProd, readDiv, readPow  :: Lit r => Parser (r -> r -> r)
readOr = parseSymbol Or >> return (#||)
readAnd = parseSymbol And >> return (#&&)
readEq = parseSymbol Eq >> return (#==)
readNe = parseSymbol Ne >> return (#!=)
readLt = parseSymbol Lt  >> return (#<)
readGt = parseSymbol Gt >> return (#>)
readLe = parseSymbol Le >> return (#<=)
readGe = parseSymbol Ge >> return (#>=)
readAdd = parseSymbol Add >> return (#+)
readSub = parseSymbol Sub >> return (#-)
readProd = parseSymbol Mul >> return (#*)
readDiv = parseSymbol Div >> return (#/)
readPow = parseSymbol Pow >> return (#^)


-- | Show binary operators
showBinop :: S.Binop -> ShowS
showBinop S.Add   = showSymbol Add
showBinop S.Sub   = showSymbol Sub
showBinop S.Prod  = showSymbol Mul
showBinop S.Div   = showSymbol Div
showBinop S.Pow   = showSymbol Pow
showBinop S.And   = showSymbol And
showBinop S.Or    = showSymbol Or
showBinop S.Lt    = showSymbol Lt
showBinop S.Gt    = showSymbol Gt
showBinop S.Eq    = showSymbol Eq
showBinop S.Ne    = showSymbol Ne
showBinop S.Le    = showSymbol Le
showBinop S.Ge    = showSymbol Ge


-- | Parse and show unary operators
readNeg, readNot :: Lit r => Parser (r -> r)
readNeg = parseSymbol Neg >> return neg_
readNot = parseSymbol Not >> return not_

showUnop :: S.Unop -> ShowS
showUnop S.Neg = showSymbol Neg
showUnop S.Not = showSymbol Not
        
        
-- | Printer for literal syntax
instance Num Printer where
  fromInteger = printP . shows
  (+) = error "Num Printer"
  (-) = error "Num Printer"
  (*) = error "Num Printer"
  abs = error "Num Printer"
  negate = error "Num Printer"
  signum = error "Num Printer"
  
instance Fractional Printer where
  fromRational = printP . shows
  (/) = error "Num Printer"
  
instance IsString Printer where
  fromString s = printP (showChar '"' . showLitString s . showChar '"')
  
printUnop :: S.Unop -> Printer -> Printer
printUnop o (P prec s) =
  P (Unop o) (showUnop o . showParen (test prec) s)
  where
    test (Binop _) = True
    --test Use = True
    test _ = False
    
printBinop :: S.Binop -> Printer -> Printer -> Printer
printBinop o (P prec1 s1) (P prec2 s2) =
    P (Binop o) (showParen (test prec1) s1 . showChar ' '
      . showBinop o . showChar ' ' . showParen (test prec2) s2)
    where
      test (Binop p) = S.prec o p
      --test Use = True
      test _ = False
  
instance Un_ Printer where
  not_ = printUnop S.Not
  neg_ = printUnop S.Neg
  
instance Arith_ Printer where
  (#+) = printBinop S.Add
  (#-) = printBinop S.Sub
  (#*) = printBinop S.Prod
  (#/) = printBinop S.Div
  (#^) = printBinop S.Pow
  
instance Cmp_ Printer where
  (#==) = printBinop S.Eq
  (#!=) = printBinop S.Ne
  (#<)  = printBinop S.Lt
  (#<=) = printBinop S.Le
  (#>)  = printBinop S.Gt
  (#>=) = printBinop S.Ge
  
instance Logic_ Printer where
  (#||) = printBinop S.Or
  (#&&) = printBinop S.And
  
  
-- | Parse a local name
local :: Local r => Parser r
local = local_ <$> ident


-- | Parse a public name
self :: Self r => Parser r
self = self_ <$> (point *> ident)


-- | Parse an external name
use :: Extern r => Parser r
use = use_ <$> (P.string "@use" *> spaces *> ident)

  
-- | Parse a field
field :: Field r => Parser (Compound r -> r)
field = parseField


instance Self Printer where
  self_ i = printP (showString "." . showIdent i)
  
instance Local Printer where
  local_ = printP . showIdent
  
instance Extern Printer where
  use_ i = P Use (showString "@use " . showIdent i)

instance Field_ Printer where
  type Compound Printer = Printer
  P prec s #. i = printP (showParen (test prec) s . showString "." . showIdent i) where
    test Lit = False
    test Use = False
    test Esc = False
    test _ = True


-- | Parse a value extension
extend :: Extend r => Parser (r -> Ext r -> r)
extend = pure (#)

instance Extend Printer where
  type Ext Printer = Printer
  P prec1 s1 # P prec2 s2 =
    printP (showParen (test prec1) s1 . showParen (test prec2) s2) 
    where
      test Lit = False
      test Use = False
      test Esc = False
      test _ = True
  
  
-- | Parse a expression 'escape' operator
esc :: Esc r => Parser (Lower r -> r)
esc = P.char '^' >> spaces >> return esc_

instance Esc Printer where
  type Lower Printer = Printer
  esc_ (P prec s) = P Esc (showString "^" . showParen (test prec) s)
    where
      test Lit = False
      test Use = False
      test Esc = False
      test _   = True
  
-- | Parse statement equals definition
assign :: Let r => Parser (Lhs r -> Rhs r -> r)
assign = P.char '=' >> spaces >> return (#=)
            
    
-- | Parse statement separators
stmtsep :: Parser ()
stmtsep = P.char ';' >> spaces
  
    
  
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
  
instance Field_ ARelPath where
  type Compound ARelPath = ARelPath
  ARelPath p #. k = ARelPath (p #. k) 
  
instance Local ALocalPath where
  local_ i = ALocalPath (local_ i)
  
instance Field_ ALocalPath where
  type Compound ALocalPath = ALocalPath
  ALocalPath p #. k = ALocalPath (p #. k)


-- | Parse an expression observing operator precedence
orexpr :: (Lit r, Esc r, Lower r ~ r) => Parser r -> Parser r
orexpr p = parseLogic (cmpexpr p)
-- orexpr p = P.chainl1 (andexpr p) readOr

andexpr :: (Lit r, Esc r, Lower r ~ r) => Parser r -> Parser r
andexpr p = P.chainl1 (cmpexpr p) readAnd
        
cmpexpr :: (Lit r, Esc r, Lower r ~ r) => Parser r -> Parser r
cmpexpr p = parseCmp (addexpr p)
{-
cmpexpr p =
  do
    a <- addexpr p
    (do
       s <- op
       b <- addexpr p
       return (s a b))
      <|> return a
  where
    op = readGt <|> readLt <|> readEq <|> readNe <|> readGe <|> readLe
-}
      
addexpr :: (Lit r, Esc r, Lower r ~ r) => Parser r -> Parser r
addexpr p = parseArith (unopexpr p)
--  P.chainl1 (mulexpr p) (readAdd <|> readSub)

mulexpr :: (Lit r, Esc r, Lower r ~ r) => Parser r -> Parser r
mulexpr p =
  P.chainl1 (unopexpr p) (readProd <|> readDiv)

powexpr :: (Lit r, Esc r, Lower r ~ r) => Parser r -> Parser r
powexpr p = P.chainl1 (unopexpr p) readPow
          
          
-- | Parse an unary operation
unopexpr :: Lit r => Parser r -> Parser r
unopexpr p = parseUn <*> p
--  ((readNot <|> readNeg) <*> unopexpr p) <|> p


-- | Parse a chain of field accesses and extensions
pathexpr
 :: forall r
  . ( Expr r
    , Extern r
    , Decl (Stmt r), LetPatt (Stmt r)
    , Pun (Stmt r), Esc r, Lower r ~ r
    )
 => Parser r -> Parser r
pathexpr p =
  first <**> rest
  where
    step =
      liftA2 flip extend (block (stmt p))   -- '(' ...
                                            -- '{' ...
        <|> field                           -- '.' ...
    
    rest = iter step
    
    first =
      string                  -- '"' ...
        <|> number            -- digit ...
        <|> local             -- alpha ...
        <|> self              -- '.' alpha ...
        <|> use               -- '@' ...
        <|> (esc <*> first)   -- '^' ...
        <|> parens p          -- '(' ...
        <|> block (stmt p)    -- '{' ...    
        
        

syntax
 :: ( Expr r
    , Extern r
    , Decl (Stmt r), LetPatt (Stmt r), Pun (Stmt r))
 => Parser r
syntax = cmpexpr term where
  term = 
    pathexpr syntax   -- '"' ...
                      -- digit ...
                      -- '.' alpha ...
                      -- alpha ...
                      -- '@' ...
                      -- '(' ...
                      -- '{' ...


-- | Parse different bracket types
braces :: Parser a -> Parser a
braces =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)

    
parens :: Parser a -> Parser a
parens =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    

staples :: Parser a -> Parser a
staples =
  P.between
    (P.char '[' >> spaces)
    (P.char ']' >> spaces)
    
-- | Parse a block construction
block :: Block r => Parser (Stmt r) -> Parser r
block s = block_ <$> braces stmts <?> "block" where
  stmts = P.sepEndBy s stmtsep
  

instance Block Printer where
  type Stmt Printer = Printer
  
  block_ []     = printP (showString "{}")
  block_ (s:ss) = printP (showString "{" . showP s . showString ";"
    . appEndo (foldMap
      (\ s -> Endo (showString " " . showP s . showString ";"))
      ss)
    . showString "}")
      
    

-- | Parse a statement of a block expression
stmt :: (Decl s, LetPatt s, Pun s) => Parser (Rhs s) -> Parser s
stmt p =
  pubfirst          -- '.' alpha ...
    <|> pattfirst   -- alpha ...
                    -- '(' ...
    <|> escfirst    -- '^' ...
    <?> "statement"
  where
    pubfirst = do
      ARelPath apath <- relpath
      ((`id` apath) <$> pattrest <**> assign <*> p  -- '{' ...
                                                    -- '=' ...
        <|> return apath)
      
    pattfirst =
      (localpath      -- alpha ...
        <|> pattblock)  -- '{' ...
        <**> pattrest <**> assign <*> p
      
    pattrest :: Patt p => Parser (p -> p)
    pattrest = iter (liftA2 flip extend pattblock)
          
    pattblock
      :: (Block p, Pun (Stmt p), LetMatch (Stmt p), Patt (Lower (Rhs (Stmt p))))
      => Parser p
    pattblock = block (match patt) 
    
    patt :: Patt p => Parser p 
    patt =
      (relpath          -- '.' alpha
        <|> localpath   -- alpha
        <|> pattblock)  -- '{'
        <**> pattrest
        <?> "pattern"
        
    escfirst = esc <*>
      (localpath         -- '.' alpha ..
        <|> relpath)     -- alpha ...
    
-- | Parse a statement of a pattern block
match
  :: (LetMatch s, Pun s) => Parser (Lower (Rhs s)) -> Parser s
match p =
  escfirst         -- '^'
    <|> pubfirst   -- '.' alpha
  where
    escfirst = esc <*>
      (localpath         -- alpha ...
        <|> relpath)     -- '.' alpha ...
  
    pubfirst = 
      flip id <$> relpath <*> assign <*> (esc <*> p)
      
instance Let Printer where
  type Lhs Printer = Printer
  type Rhs Printer = Printer
  p1 #= p2 = printP (showP p1 . showString " = " . showP p2)
    
    
-- | Parse a top-level sequence of statements
program'
  :: (Decl s, LetPatt s, Pun s
  , Extern (Rhs s)
  , Expr (Rhs s), Stmt (Rhs s) ~ s)
  => Parser [s]
program' = spaces *> body <* P.eof where
  body = P.sepEndBy (stmt syntax) stmtsep


showProgram' :: [Printer] -> ShowS
showProgram' []     = id
showProgram' (s:ss) = showP s . showString ";\n"
  . appEndo (foldMap
      (\ s -> Endo (showString "\n" . showP s . showString ";\n"))
      ss)
      
      
-- | Preface '@imports' section
imports :: (Imports r, LetImport (ImportStmt r)) => Parser (Imp r -> r)
imports = P.string "@imports" *> spaces *> (extern_ <$> importstmts)
  where
    importstmts = P.sepEndBy letimport stmtsep
    letimport = flip id <$> local <*> assign <*> string
    
    
-- | Preface '@include' section
include :: Include r => Parser (Inc r -> r)
include = P.string "@include" *> spaces *> (include_ <$> ident)


-- | Preface '@module' section
modul :: Module r => Parser ([ModuleStmt r] -> r)
modul = P.string "@module" *> spaces *> pure module_ 


-- | Program preface
preface 
 :: (Preface r, LetImport (ImportStmt r))
 => Parser ([ModuleStmt r] -> r)
preface =
  importsFirst
    <|> includeFirst
    <|> moduleFirst
    <|> pure module_
  where
    importsFirst
     :: ( Imports r, LetImport (ImportStmt r)
        , Module (Imp r), Include (Imp r), Module (Inc (Imp r))
        , ModuleStmt (Inc (Imp r)) ~ ModuleStmt (Imp r)
        )
     => Parser ([ModuleStmt (Imp r)] -> r)
    importsFirst = 
      liftA2 (.) imports (includeFirst <|> moduleFirst)
    
    includeFirst
     :: (Include r, Module (Inc r))
     => Parser ([ModuleStmt (Inc r)] -> r)
    includeFirst =
      liftA2 (.) include moduleFirst
    
    moduleFirst :: Module r => Parser ([ModuleStmt r] -> r)
    moduleFirst = modul
      
    
program
 :: ( Preface r, LetImport (ImportStmt r)
    , Decl (ModuleStmt r), LetPatt (ModuleStmt r)
    , Pun (ModuleStmt r)
    , Extern (Rhs (ModuleStmt r)), Expr (Rhs (ModuleStmt r))
    , Stmt (Rhs (ModuleStmt r)) ~ ModuleStmt r)
 => Parser r
program = preface <*> program'
    


-- Util printers
showLitString :: String -> ShowS
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)

showLitText :: T.Text -> ShowS
showLitText = showLitString . T.unpack

showText :: T.Text -> ShowS
showText = (++) . T.unpack
