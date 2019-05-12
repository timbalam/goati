{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, DeriveFunctor, LambdaCase #-}
module Goat.Lang.Parser.Block where
import Goat.Lang.Parser.Token
import qualified Goat.Lang.Parser.Path as PATH
import qualified Goat.Lang.Parser.Pattern as PATTERN
import Goat.Lang.Class
import Goat.Util ((...))
import Control.Monad.Free (wrap, Free(..))
import Data.Bifunctor (first)
import Data.Function (on)
import Data.Functor (($>))
import Data.Void (Void)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
{-
Block
-----

A *BLOCK* is a sequence of *STMT*s separated and optionally terminated by literal semi-colons (';').
A source file will often consist of a single block.

    BLOCK := [STMT [';' BLOCK]]
-}

-- We can represent a *BLOCK* as a concrete Haskell datatype.

data BLOCK a = BLOCK_END | BLOCK_STMT (STMT a) (BLOCK_STMT a)
  deriving Functor
data BLOCK_STMT a = BLOCK_STMTEND | BLOCK_STMTSEP (BLOCK a)
  deriving Functor

-- and implement the 'Block_' Goat syntax interface (see 'Goat.Lang.Class')

--proofBlock :: BLOCK DEFINITION -> BLOCK DEFINITION
--proofBlock = parseBlock

-- To parse: 

block :: Parser (BLOCK DEFINITION)
block = (do
  a <- stmt
  b <- blockStmt
  return (BLOCK_STMT a b)) <|>
  return BLOCK_END

blockStmt :: Parser (BLOCK_STMT DEFINITION)
blockStmt = blockStmtSep <|> return BLOCK_STMTEND
  where
    blockStmtSep =
      punctuation SEP_SEMICOLON >>
      (BLOCK_STMTSEP <$> block)

-- We can convert the parse result to syntax as described in 'Goat.Lang.Class'

parseBlock
 :: (Block_ r, Definition_ (Rhs (Item r)))
 => BLOCK DEFINITION -> r
parseBlock b = fromList (toList b) where
  toList BLOCK_END = []
  toList (BLOCK_STMT a b) = case b of
    BLOCK_STMTEND   -> [parseStmt a]
    BLOCK_STMTSEP b -> parseStmt a : toList b

-- and show it as a grammatically valid string

showBlock :: ShowS -> BLOCK DEFINITION -> ShowS
showBlock wsep BLOCK_END = wsep
showBlock wsep (BLOCK_STMT a b) =
  wsep .
  showStmt a .
  showBlockStmt wsep b

showBlockStmt :: ShowS -> BLOCK_STMT DEFINITION -> ShowS
showBlockStmt _wsep BLOCK_STMTEND = id
showBlockStmt wsep (BLOCK_STMTSEP b) =
  showPunctuation SEP_SEMICOLON . showBlock wsep b

-- Implementing the Goat syntax interface

instance IsList (BLOCK a) where
  type Item (BLOCK a) = STMT a
  fromList [] = BLOCK_END
  fromList (s:ss) =
    BLOCK_STMT s (BLOCK_STMTSEP (fromList ss))
  toList = error "IsList (Maybe BLOCK): toList"

{-
Statement
---------

In terms of Goat's grammar a *STMT* ('statement')
can have a few forms.
The first form starts with a *PATH*,
and can optionally be continued by a *PATTERNBLOCKS*,
an equals sign ('='),
and a *DEFINITION*,
or alternatively by an equals sign ('=') and a *DEFINITION*.
The second form starts with *PATTERNBLOCKS*,
and finishes with an equals sign ('=') and a *DEFINITION*.

    STMT :=
        PATH [PATTERNBLOCKS '=' DEFINITION]
      | '{' PATTERNBLOCK '}' PATTERNBLOCKS '=' DEFINITION
-}

-- A datatype concretely representing a *STMT*,
-- implementing the Goat syntax interface 'Stmt_',
-- is below.

data STMT a =
    STMT_PATH PATH.PATH (STMT_PATH a)
  | STMT_BLOCKDELIMEQ
      (PATTERN.PATTERNBLOCK PATTERN.PATTERN)
      (PATTERN.PATTERNBLOCKS PATTERN.PATTERN)
      a
  deriving Functor
data STMT_PATH a =
    STMT_PATHEND
  | STMT_PATHEQ (PATTERN.PATTERNBLOCKS PATTERN.PATTERN) a
  deriving Functor

-- proofStmt :: STMT a -> STMT a
-- proofStmt = parseStmt

-- We can parse with

stmt :: Parser (STMT DEFINITION)
stmt = pathNext <|> blockNext where
  pathNext = do
    a <- PATH.path
    b <- stmtPath
    return (STMT_PATH a b)
  blockNext = do
    punctuation LEFT_BRACE
    a <- PATTERN.patternBlock
    punctuation RIGHT_BRACE
    b <- PATTERN.patternBlocks
    symbol "="
    c <- definition
    return (STMT_BLOCKDELIMEQ a b c)
  
  stmtPath :: Parser (STMT_PATH DEFINITION)
  stmtPath = (do
    a <- PATTERN.patternBlocks
    symbol "="
    b <- definition
    return (STMT_PATHEQ a b)) <|>
    return STMT_PATHEND

-- We can convert the parse result to syntax with

parseStmt
 :: (Stmt_ r, Definition_ (Rhs r)) => STMT DEFINITION -> r
parseStmt = \case
  STMT_PATH a STMT_PATHEND -> 
    PATH.parsePath a
  
  STMT_PATH a (STMT_PATHEQ bs c) ->
    PATTERN.parsePattern (PATTERN.PATTERN_PATH a bs) #=
      parseDefinition c
    
  STMT_BLOCKDELIMEQ a bs c ->
    PATTERN.parsePattern (PATTERN.PATTERN_BLOCKDELIM a bs) #=
      parseDefinition c

-- and show the grammar as a string

showStmt :: STMT DEFINITION -> ShowS
showStmt (STMT_PATH a b) =
  PATH.showPath a . showStmtPath b
showStmt (STMT_BLOCKDELIMEQ a b c) =
  showPunctuation LEFT_BRACE .
  PATTERN.showPatternBlock (showChar ' ') a .
  showPunctuation RIGHT_BRACE .
  PATTERN.showPatternBlocks b .
  showSymbolSpaced (SYMBOL "=") .
  showDefinition c

showStmtPath :: STMT_PATH DEFINITION -> ShowS
showStmtPath STMT_PATHEND = id
showStmtPath (STMT_PATHEQ a b) =
  PATTERN.showPatternBlocks a .
  showSymbolSpaced (SYMBOL "=") .
  showDefinition b

-- We need the following Goat syntax interfaces implemented for our grammar representation.

instance IsString (STMT a) where
  fromString s = STMT_PATH (fromString s) STMT_PATHEND

instance Select_ (STMT a) where
  type Selects (STMT a) = Either PATH.Self PATH.PATH
  type Key (STMT a) = IDENTIFIER
  c #. i = STMT_PATH (c #. i) STMT_PATHEND

instance Assign_ (STMT a) where
  type Lhs (STMT a) = PATTERN.PATTERN
  type Rhs (STMT a) = a
  PATTERN.PATTERN_PATH a b #= r = STMT_PATH a (STMT_PATHEQ b r)
  PATTERN.PATTERN_BLOCKDELIM a b #= r = STMT_BLOCKDELIMEQ a b r

{-
Definition
----------

A *DEFINITION* is an *OREXPR*.
An *OREXPR* is a non-empty sequence of *ANDEXPR*s,
separated by double-bars ('||').
An *ANDEXPR* is a non-empty sequence of *COMPAREEXPR*s,
separated by double-and signs ('&&').
A *COMPAREEXPR* is a *POWEXPR*,
optionally followed by a *COMPAREOP* and a *SUMEXPR*.
A *COMPAREOP* is either a double-equal sign ('=='),
an exclamation mark and equal sign ('!='),
a less-than sign ('<'),
a less-than sign and equal sign ('<='),
a greater-than sign ('>'),
or a greater-than sign and equal sign ('>=').
A *SUMEXPR* is a non-empty sequence of *PRODEXPR*s,
separated by *SUMOP*s.
A *SUMOP* is a plus sign ('+') or minus sign ('-').
A *PRODEXPR* is a non-empty sequence of *POWEXPR*s,
separated by *PRODOP*s.
A *PRODOP* is either an asterisk ('*') or a slash ('/').
A *POWEXPR* is a non-empty sequence of *UNARYEXPR*s,
separated by carets ('^').
A *UNARYEXPR* is an optional *UNARYOP*,
followed by  a *TERM*. 
A *UNARYOP* is either an exclamation mark ('!'),
or a minus sign ('-').
A *TERM* is either a *NUMBERLITERAL* or a *FIELDEXPR*.
A *FIELDEXPR* is an *ORIGIN*,
optionally followed by a sequence of *MODIFIERS*.
An *ORIGIN* can be a *TEXTLITERAL*, a *FIELD*,
an *IDENTIFIER*, a *BLOCK* delimited by braces ('{'), ('}'),
or a *DEFINITION* delimited by parentheses ('('), (')').
A *MODIFIER* is either a *FIELD* or a brace-delimited *BLOCK*.

    DEFINITION := OREXPR
    OREXPR := ANDEXPR ['||' OREXPR]
    ANDEXPR := COMPAREEXPR ['&&' ANDEXPR]
    COMPAREEXPR := SUMEXPR [COMPAREOP SUMEXPR]
    COMPAREOP := '==' | '!=' | '<' | '<=' | '>' | '>='
    SUMEXPR := PRODEXPR [SUMOP SUMEXPR]
    SUMOP := '+' | '-'
    PRODEXPR := POWEXPR [PRODOP PRODEXPR]
    PRODOP := '*' | '/'
    POWEXPR := UNARYEXPR ['^' POWEXPR]
    UNARYEXPR := [UNARYOP] TERM
    UNARYOP := '-' | '!'
    TERM := NUMBERLITERAL | ORIGIN MODIFIERS
    ORIGIN :=
        TEXTLITERAL
      | IDENTIFIER
      | FIELD
      | '{' BLOCK '}'
      | '(' DEFINITION ')'
    MODIFIERS := [(FIELD MODIFIERS | '{' BLOCK '}' MODIFIERS)]
-}

-- Our concrete representation captures the associativity and 
-- precedence of the operators defined by  the Goat syntax interface.

newtype DEFINITION = DEFINITION (OREXPR DEFINITION)
data OREXPR a = EXPR_AND (ANDEXPR a) (OREXPR_AND a)
data OREXPR_AND a = EXPR_ANDEND | EXPR_OROP (OREXPR a)
data ANDEXPR a = EXPR_COMPARE (COMPAREEXPR a) (ANDEXPR_COMPARE a)
data ANDEXPR_COMPARE a =
  EXPR_COMPAREEND | EXPR_ANDOP (ANDEXPR a)
data COMPAREEXPR a = EXPR_SUM (SUMEXPR a) (COMPAREEXPR_SUM a)
data COMPAREEXPR_SUM a =
  EXPR_SUMEND |
  EXPR_EQOP (SUMEXPR a) |
  EXPR_NEOP (SUMEXPR a) |
  EXPR_LTOP (SUMEXPR a) |
  EXPR_LEOP (SUMEXPR a) |
  EXPR_GTOP (SUMEXPR a) |
  EXPR_GEOP (SUMEXPR a)
data SUMEXPR a = EXPR_PROD (SUMEXPR_SUM a) (PRODEXPR a)
data SUMEXPR_SUM a =
    EXPR_SUMSTART
  | EXPR_ADDOP (SUMEXPR a)
  | EXPR_SUBOP (SUMEXPR a)
data PRODEXPR a = EXPR_POW (PRODEXPR_PROD a) (POWEXPR a)
data PRODEXPR_PROD a =
  EXPR_PRODSTART |
  EXPR_MULOP (PRODEXPR a) |
  EXPR_DIVOP (PRODEXPR a)
data POWEXPR a = EXPR_UNARY (UNARYEXPR a) (POWEXPR_UNARY a)
data POWEXPR_UNARY a =
  EXPR_UNARYEND |
  EXPR_POWOP (POWEXPR a)
data UNARYEXPR a =
  EXPR_TERM (TERM a) |
  EXPR_NEGOP (TERM a) |
  EXPR_NOTOP (TERM a)
data TERM a =
  EXPR_NUMBER NUMLITERAL |
  EXPR_ORIGIN (ORIGIN a) (MODIFIERS a)
data ORIGIN a =
  EXPR_TEXT TEXTLITERAL |
  EXPR_BLOCKDELIM (BLOCK a) |
  EXPR_IDENTIFIER IDENTIFIER |
  EXPR_FIELD PATH.FIELD |
  EXPR_EXPRDELIM a
data MODIFIERS a =
  MODIFIERS_START |
  MODIFIERS_SELECTOP (MODIFIERS a) IDENTIFIER |
  MODIFIERS_EXTENDDELIMOP (MODIFIERS a) (BLOCK a)

-- proofDefinition :: DEFINITION -> DEFINITION
-- proofDefinition = parseDefinition

-- To parse

definition :: Parser DEFINITION
definition = DEFINITION <$> orExpr

orExpr :: Parser (OREXPR DEFINITION)
orExpr = tokInfixR f andExpr op where
  f a = EXPR_AND a EXPR_ANDEND
  op = symbol "||" $> \ a b -> EXPR_AND a (EXPR_OROP b)

andExpr :: Parser (ANDEXPR DEFINITION)
andExpr = tokInfixR f compareExpr op where
  f a = EXPR_COMPARE a EXPR_COMPAREEND
  op = symbol "&&" $> \ a b -> EXPR_COMPARE a (EXPR_ANDOP b)

compareExpr :: Parser (COMPAREEXPR DEFINITION)
compareExpr = tokInfix f sumExpr op where
  f a = EXPR_SUM a EXPR_SUMEND
  op =
    (symbol ">" $> mkOp EXPR_GTOP) <|>
    (symbol "<" $> mkOp EXPR_LTOP) <|>
    (symbol "==" $> mkOp EXPR_EQOP) <|>
    (symbol "!=" $> mkOp EXPR_NEOP) <|>
    (symbol ">=" $> mkOp EXPR_GEOP) <|>
    (symbol "<=" $> mkOp EXPR_LEOP)
  mkOp f a b = EXPR_SUM a (f b)

sumExpr :: Parser (SUMEXPR DEFINITION)
sumExpr = tokInfixL f prodExpr op where
  f a = EXPR_PROD EXPR_SUMSTART a
  op = 
    (symbol "+" $> mkOp EXPR_ADDOP) <|>
    (symbol "-" $> mkOp EXPR_SUBOP)
  mkOp f a b = EXPR_PROD (f a) b

prodExpr :: Parser (PRODEXPR DEFINITION)
prodExpr = tokInfixL f powExpr op where 
  f = EXPR_POW EXPR_PRODSTART
  op =
    (symbol "*" $> mkOp EXPR_MULOP) <|>
    (symbol "/" $> mkOp EXPR_DIVOP)
  mkOp f a b = EXPR_POW (f a) b

powExpr :: Parser (POWEXPR DEFINITION)
powExpr = tokInfixR f unaryExpr op where
  f a = EXPR_UNARY a EXPR_UNARYEND
  op = symbol "^" $> \ a b -> EXPR_UNARY a (EXPR_POWOP b)

unaryExpr :: Parser (UNARYEXPR DEFINITION)
unaryExpr = (op <|> return EXPR_TERM) <*> term where
  op =
   (symbol "-" $> EXPR_NEGOP) <|>
   (symbol "!" $> EXPR_NOTOP)

term :: Parser (TERM DEFINITION)
term = numberNext <|> originNext
  where
   numberNext = EXPR_NUMBER <$> numLiteral
   originNext = do
     a <- origin
     b <- modifiers
     return (EXPR_ORIGIN a b)

origin :: Parser (ORIGIN DEFINITION)
origin =
  (EXPR_TEXT <$> textLiteral) <|>
  (EXPR_IDENTIFIER <$> identifier) <|>
  (EXPR_FIELD <$> PATH.field) <|>
  blockNext <|>
  nestedNext
  where
    blockNext =
      EXPR_BLOCKDELIM <$>
      Parsec.between
        (punctuation LEFT_BRACE)
        (punctuation RIGHT_BRACE)
        block
    nestedNext =
      EXPR_EXPRDELIM <$>
      Parsec.between
        (punctuation LEFT_PAREN)
        (punctuation RIGHT_PAREN)
        definition

modifiers :: Parser (MODIFIERS DEFINITION)
modifiers = go MODIFIERS_START where
  go a = fieldNext a <|> blockNext a <|> return a
  fieldNext a = do
    symbol "."
    i <- identifier
    go (MODIFIERS_SELECTOP a i)
  blockNext a = do
    x <-
      Parsec.between
        (punctuation LEFT_BRACE)
        (punctuation RIGHT_BRACE)
        block
    go (MODIFIERS_EXTENDDELIMOP a x)

tokInfixR
 :: (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
tokInfixR f p op = do
  a <- p
  (do
    s <- op
    b <- tokInfixR f p op
    return (s a b)) <|>
    return (f a)

tokInfix
 :: (a -> b) -> Parser a -> Parser (a -> a -> b) -> Parser b
tokInfix f p op = do
  a <- p
  (do
     s <- op
     b <- p
     return (s a b)) <|>
     return (f a)

tokInfixL
 :: (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
tokInfixL f p op = do a <- p; rest (f a) where
  rest a = (do
    s <- op
    b <- p
    rest (s a b)) <|>
    return a

-- For converting to syntax

parseDefinition :: Definition_ r => DEFINITION -> r
parseDefinition (DEFINITION a) = parseOrExpr a

parseOrExpr :: Definition_ r => OREXPR DEFINITION -> r
parseOrExpr (EXPR_AND a EXPR_ANDEND) = parseAndExpr a
parseOrExpr (EXPR_AND a (EXPR_OROP b)) =
  parseAndExpr a #|| parseOrExpr b

parseAndExpr :: Definition_ r => ANDEXPR DEFINITION -> r
parseAndExpr (EXPR_COMPARE a EXPR_COMPAREEND) = 
  parseCompareExpr a
parseAndExpr (EXPR_COMPARE a (EXPR_ANDOP b)) =
  parseCompareExpr a #&& parseAndExpr b

parseCompareExpr :: Definition_ r => COMPAREEXPR DEFINITION -> r
parseCompareExpr (EXPR_SUM a b) =
  case b of
    EXPR_SUMEND -> parseSumExpr a
    EXPR_EQOP b -> op (#==) a b
    EXPR_NEOP b -> op (#!=) a b
    EXPR_LTOP b -> op (#<) a b
    EXPR_LEOP b -> op (#<=) a b
    EXPR_GTOP b -> op (#>) a b
    EXPR_GEOP b -> op (#>=) a b
  where
    op f = f `on` parseSumExpr

parseSumExpr :: Definition_ r => SUMEXPR DEFINITION -> r
parseSumExpr (EXPR_PROD a b) =
  case a of
    EXPR_SUMSTART -> parseProdExpr b
    EXPR_ADDOP a -> op (+) a b
    EXPR_SUBOP a -> op (-) a b
  where
    op f a b = parseSumExpr a `f` parseProdExpr b

parseProdExpr :: Definition_ r => PRODEXPR DEFINITION -> r
parseProdExpr (EXPR_POW a b) =
  case a of
    EXPR_PRODSTART -> parsePowExpr b
    EXPR_MULOP a -> op (*) a b
    EXPR_DIVOP a -> op (/) a b
  where
    op f a b = parseProdExpr a `f` parsePowExpr b

parsePowExpr :: Definition_ r => POWEXPR DEFINITION -> r
parsePowExpr (EXPR_UNARY a EXPR_UNARYEND) = parseUnaryExpr a
parsePowExpr (EXPR_UNARY a (EXPR_POWOP b)) =
  parseUnaryExpr a #^ parsePowExpr b

parseUnaryExpr :: Definition_ r => UNARYEXPR DEFINITION -> r
parseUnaryExpr (EXPR_NEGOP a) = neg_ (parseTerm a)
parseUnaryExpr (EXPR_NOTOP a) = not_ (parseTerm a)
parseUnaryExpr (EXPR_TERM a) = parseTerm a

parseTerm :: Definition_ r => TERM DEFINITION -> r
parseTerm (EXPR_NUMBER n) = parseNumLiteral n
parseTerm (EXPR_ORIGIN a ms) = parseModifiers a ms
  where
    parseModifiers
     :: Definition_ r
     => ORIGIN DEFINITION -> MODIFIERS DEFINITION -> r
    parseModifiers a MODIFIERS_START = parseOrigin a
    parseModifiers a (MODIFIERS_SELECTOP ms i) =
      parseModifiers a ms #. parseIdentifier i
    parseModifiers a (MODIFIERS_EXTENDDELIMOP ms b) =
      parseModifiers a ms # parseBlock b

parseOrigin :: Definition_ r => ORIGIN DEFINITION -> r
parseOrigin (EXPR_TEXT t) = parseTextLiteral t
parseOrigin (EXPR_BLOCKDELIM b) = parseBlock b
parseOrigin (EXPR_IDENTIFIER i) = parseIdentifier i
parseOrigin (EXPR_FIELD a) = PATH.parseField a
parseOrigin (EXPR_EXPRDELIM e) = parseDefinition e

-- and for showing

showDefinition :: DEFINITION -> ShowS
showDefinition (DEFINITION a) = showOrExpr a

showOrExpr :: OREXPR DEFINITION -> ShowS
showOrExpr (EXPR_AND a EXPR_ANDEND) = showAndExpr a
showOrExpr (EXPR_AND a (EXPR_OROP b)) =
  showAndExpr a .
  showSymbolSpaced (SYMBOL "||") .
  showOrExpr b

showAndExpr :: ANDEXPR DEFINITION -> ShowS
showAndExpr (EXPR_COMPARE a EXPR_COMPAREEND) =
  showCompareExpr a
showAndExpr (EXPR_COMPARE a (EXPR_ANDOP b)) =
  showCompareExpr a .
  showSymbolSpaced (SYMBOL "&&") .
  showAndExpr b

showCompareExpr :: COMPAREEXPR DEFINITION -> ShowS
showCompareExpr (EXPR_SUM a b) =
  case b of
    EXPR_SUMEND -> showSumExpr a
    EXPR_EQOP b -> op "==" a b
    EXPR_NEOP b -> op "!=" a b
    EXPR_LTOP b -> op "<" a b
    EXPR_LEOP b -> op "<=" a b
    EXPR_GTOP b -> op ">" a b
    EXPR_GEOP b -> op ">=" a b
  where
    op s a b =
      showSumExpr a .
      showSymbolSpaced (SYMBOL s) .
      showSumExpr b

showSumExpr :: SUMEXPR DEFINITION -> ShowS
showSumExpr (EXPR_PROD a b) = 
  case a of
    EXPR_SUMSTART -> showProdExpr b
    EXPR_ADDOP a -> op "+" a b
    EXPR_SUBOP a -> op "-" a b
  where
    op s a b =
      showSumExpr a .
      showSymbolSpaced (SYMBOL s) .
      showProdExpr b

showProdExpr :: PRODEXPR DEFINITION -> ShowS
showProdExpr (EXPR_POW a b) = 
  case a of
    EXPR_PRODSTART -> showPowExpr b
    EXPR_MULOP a -> op "*" a b
    EXPR_DIVOP a -> op "/" a b
  where
    op s a b =
      showProdExpr a .
      showSymbolSpaced (SYMBOL s) .
      showPowExpr b

showPowExpr :: POWEXPR DEFINITION -> ShowS
showPowExpr (EXPR_UNARY a EXPR_UNARYEND) = showUnaryExpr a
showPowExpr (EXPR_UNARY a (EXPR_POWOP b)) =
  showUnaryExpr a .
  showSymbolSpaced (SYMBOL "^") .
  showPowExpr b

showUnaryExpr :: UNARYEXPR DEFINITION -> ShowS
showUnaryExpr a =
  case a of
    EXPR_TERM a -> showTerm a
    EXPR_NEGOP a -> op "-" a
    EXPR_NOTOP a -> op "!" a
  where
    op s a =
      showSymbolSpaced (SYMBOL s) . 
      showTerm a

showTerm :: TERM DEFINITION -> ShowS
showTerm (EXPR_NUMBER n) = showNumLiteral n
showTerm (EXPR_ORIGIN a b) = showOrigin a . showModifiers b

showOrigin :: ORIGIN DEFINITION -> ShowS
showOrigin (EXPR_TEXT t) = showTextLiteral t
showOrigin (EXPR_BLOCKDELIM b) =
  showPunctuation LEFT_BRACE .
  showBlock (showString "\n    ") b .
  showPunctuation RIGHT_BRACE
showOrigin (EXPR_IDENTIFIER i) = showIdentifier i
showOrigin (EXPR_FIELD f) = PATH.showField f
showOrigin (EXPR_EXPRDELIM e) =
  showPunctuation LEFT_PAREN .
  showDefinition e .
  showPunctuation RIGHT_PAREN

showModifiers :: MODIFIERS DEFINITION -> ShowS
showModifiers MODIFIERS_START = id
showModifiers (MODIFIERS_SELECTOP ms i) =
  showModifiers ms .
  showSymbol (SYMBOL ".") .
  showIdentifier i
showModifiers (MODIFIERS_EXTENDDELIMOP ms b) =
  showModifiers ms .
  showPunctuation LEFT_BRACE .
  showBlock (showString "\n    ") b .
  showPunctuation RIGHT_BRACE

-- To implement the Goat syntax interface, 
-- we define a canonical expression representation.

data Canonical a =
  Number NUMLITERAL |
  Text TEXTLITERAL |
  Block (BLOCK a) |
  Local IDENTIFIER |
  Either PATH.Self a :#. IDENTIFIER |
  a :# BLOCK a |
  a :#|| a | a :#&& a | a :#== a | a :#!= a |
  a :#< a | a :#<= a | a :#> a | a :#>= a | a :#+ a |
  a :#- a | a :#* a | a :#/ a | a :#^ a |
  Neg a | Not a
  deriving Functor

-- proofCanonical :: Free Canonical Void -> Free Canonical Void
-- proofCanonical = parseDefinition . toDefinition

-- and conversions

toDefinition :: Free Canonical Void -> DEFINITION
toDefinition a = DEFINITION (toOrExpr a)

toOrExpr :: Free Canonical Void -> OREXPR DEFINITION
toOrExpr (Free  (a :#|| b)) =
  EXPR_AND (toAndExpr a) (EXPR_OROP (toOrExpr b))
toOrExpr a = EXPR_AND (toAndExpr a) EXPR_ANDEND

toAndExpr :: Free Canonical Void -> ANDEXPR DEFINITION
toAndExpr (Free (a :#&& b)) =
  EXPR_COMPARE (toCompareExpr a) (EXPR_ANDOP (toAndExpr b))
toAndExpr a = EXPR_COMPARE (toCompareExpr a) EXPR_COMPAREEND

toCompareExpr :: Free Canonical Void -> COMPAREEXPR DEFINITION
toCompareExpr = \case
  Free (a :#< b)  -> op EXPR_LTOP a b
  Free (a :#<= b) -> op EXPR_LEOP a b
  Free (a :#> b)  -> op EXPR_GTOP a b
  Free (a :#>= b) -> op EXPR_GEOP a b
  Free (a :#== b) -> op EXPR_EQOP a b
  Free (a :#!= b) -> op EXPR_NEOP a b
  a               -> EXPR_SUM (toSumExpr a) EXPR_SUMEND
  where
    op f a b = EXPR_SUM (toSumExpr a) (f (toSumExpr b))

toSumExpr :: Free Canonical Void -> SUMEXPR DEFINITION
toSumExpr = \case
  Free (a :#+ b) -> op EXPR_ADDOP a b
  Free (a :#- b) -> op EXPR_SUBOP a b
  a              -> EXPR_PROD EXPR_SUMSTART (toProdExpr a)
  where
    op f a b = EXPR_PROD (f (toSumExpr a)) (toProdExpr b)

toProdExpr :: Free Canonical Void -> PRODEXPR DEFINITION
toProdExpr = \case
  Free (a :#* b) -> op EXPR_MULOP a b
  Free (a :#/ b) -> op EXPR_DIVOP a b
  a              -> EXPR_POW EXPR_PRODSTART (toPowExpr a)
  where
    op f a b = EXPR_POW (f (toProdExpr a)) (toPowExpr b)

toPowExpr :: Free Canonical Void -> POWEXPR DEFINITION
toPowExpr (Free (a :#^ b)) =
  EXPR_UNARY (toUnaryExpr a) (EXPR_POWOP (toPowExpr b))
toPowExpr a = EXPR_UNARY (toUnaryExpr a) EXPR_UNARYEND

toUnaryExpr :: Free Canonical Void -> UNARYEXPR DEFINITION
toUnaryExpr (Free (Neg a)) = EXPR_NEGOP (toTerm a)
toUnaryExpr (Free (Not a)) = EXPR_NOTOP (toTerm a)
toUnaryExpr a = EXPR_TERM (toTerm a)

toTerm :: Free Canonical Void -> TERM DEFINITION
toTerm (Free (Number n)) = EXPR_NUMBER n
toTerm a = go EXPR_ORIGIN a
  where
    go k (Free (Right a :#. i)) = go k' a where
      k' o ms = k o (MODIFIERS_SELECTOP ms i)
    
    go k (Free (a :# x)) = go k' a where  
      k' o ms =
        k o (MODIFIERS_EXTENDDELIMOP ms (fmap toDefinition x))
    
    go k a = k (toOrigin a) MODIFIERS_START

toOrigin :: Free Canonical Void -> ORIGIN DEFINITION
toOrigin (Free (Text t)) = EXPR_TEXT t
toOrigin (Free (Block b)) = EXPR_BLOCKDELIM (fmap toDefinition b)
toOrigin (Free (Local i)) = EXPR_IDENTIFIER i
toOrigin (Free (Left PATH.Self :#. i)) =
  EXPR_FIELD (PATH.FIELD_SELECTOP i)
toOrigin a = EXPR_EXPRDELIM (toDefinition a)

-- Goat syntax interface implementation

instance IsString (Free Canonical Void) where
  fromString s = wrap (Local (fromString s))
{-
instance IsString DEFINITION where
  fromString s = toDefinition (fromString s)
-}
instance Select_ (Free Canonical Void) where
  type Selects (Free Canonical Void) =
    Either PATH.Self (Free Canonical Void)
  type Key (Free Canonical Void) = IDENTIFIER
  (#.) = wrap ... (:#.)
{-
instance Select_ DEFINITION where
  type Selects DEFINITION = Either PATH.Self DEFINITION
  type Key DEFINITION = IDENTIFIER
  a #. i = toDefinition (fmap parseDefinition a #. i)
-}
instance Operator_ (Free Canonical Void) where
  type Arg (Free Canonical Void) = Free Canonical Void
  (#||) = wrap ... (:#||)
  (#&&) = wrap ...(:#&&)
  (#==) = wrap ... (:#==)
  (#!=) = wrap ... (:#!=)
  (#>) = wrap ... (:#>)
  (#>=) = wrap ... (:#>=)
  (#<) = wrap ... (:#<)
  (#<=) = wrap ... (:#<=)
  (#+) = wrap ... (:#+)
  (#-) = wrap ... (:#-)
  (#*) = wrap ... (:#*)
  (#/) = wrap ... (:#/)
  (#^) = wrap ... (:#^)
  not_ = wrap . Not
  neg_ = wrap . Neg
{-
instance Operator_ DEFINITION where
  type Arg DEFINITION = DEFINITION
  (#||) = toDefinition ... (#||) `on` parseDefinition
  (#&&) = toDefinition ... (#&&) `on` parseDefinition
  (#==) = toDefinition ... (#==) `on` parseDefinition
  (#!=) = toDefinition ... (#!=) `on` parseDefinition
  (#>) = toDefinition ... (#>) `on` parseDefinition
  (#>=) = toDefinition ... (#>=) `on` parseDefinition
  (#<) = toDefinition ... (#<) `on` parseDefinition
  (#<=) = toDefinition ... (#<=) `on` parseDefinition
  (#+) = toDefinition ... (#+) `on` parseDefinition
  (#-) = toDefinition ... (#-) `on` parseDefinition
  (#*) = toDefinition ... (#*) `on` parseDefinition
  (#/) = toDefinition ... (#/) `on` parseDefinition
  (#^) = toDefinition ... (#^) `on` parseDefinition
  not_ = toDefinition . not_ . parseDefinition
  neg_ = toDefinition . neg_ . parseDefinition
-}
instance Extend_ (Free Canonical Void) where
  type Extends (Free Canonical Void) = Free Canonical Void
  type Extension (Free Canonical Void) =
    BLOCK (Free Canonical Void)
  (#) = wrap ... (:#)
{-
instance Extend_ DEFINITION where
  type Extends DEFINITION = DEFINITION
  type Extension DEFINITION = BLOCK DEFINITION
  a # b = toDefinition (parseDefinition a # parseBlock b)
-}
instance IsList (Free Canonical Void) where
  type Item (Free Canonical Void) = STMT (Free Canonical Void)
  fromList b = wrap (Block (fromList b))
  toList = error "IsList (Free Canonical Void): toList"
{-
instance IsList DEFINITION where
  type Item DEFINITION = STMT DEFINITION
  fromList b = toDefinition (fromList (map parseStmt b))
  toList = error "IsList DEFINITION: toList"
-}
instance TextLiteral_ (Free Canonical Void) where
  quote_ s = wrap (Text (quote_ s))
{-
instance TextLiteral_ DEFINITION where
  quote_ s = toDefinition (quote_ s)
-}
instance Num (Free Canonical Void) where
  fromInteger i = wrap (Number (fromInteger i))
  (+) = error "Num (Free Canonical Void): (+)"
  (*) = error "Num (Free Canonical Void): (*)"
  negate = error "Num (Free Canonical Void): negate"
  abs = error "Num (Free Canonical Void): abs"
  signum = error "Num (Free Canonical Void): signum"
{-
instance Num DEFINITION where
  fromInteger i = toDefinition (fromInteger i)
  (+) = error "Num DEFINITION: (+)"
  (*) = error "Num DEFINITION: (*)"
  negate = error "Num DEFINITION: negate"
  abs = error "Num DEFINITION: abs"
  signum = error "Num DEFINITION: signum"
-}
instance Fractional (Free Canonical Void) where
  fromRational i = wrap (Number (fromRational i))
  (/) = error "Fractional (Free Canonical Void): (/)"
{-
instance Fractional DEFINITION where
  fromRational i = toDefinition (fromRational i)
  (/) = error "Fractional DEFINITION: (/)"
-}