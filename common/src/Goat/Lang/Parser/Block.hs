{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, DeriveFunctor, LambdaCase, RankNTypes #-}
module Goat.Lang.Parser.Block where
import Goat.Lang.Parser.Token
import Goat.Lang.Parser.Path
import Goat.Lang.Parser.Pattern
import Goat.Lang.Class
import Goat.Util ((...))
import Data.Bifunctor (first)
import Data.Function (on)
import Data.Functor (($>))
import Data.Void (Void, absurd)
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
data BLOCK_STMT a = BLOCK_STMTEND | BLOCK_STMTSEP (BLOCK a)

-- and implement the 'Block_' Goat syntax interface (see 'Goat.Lang.Class')

proofBlock :: BLOCK a -> BLOCK a
proofBlock = parseBlock id

-- To parse: 

block :: Parser r -> Parser (BLOCK r)
block p = (do
  a <- stmt p
  b <- blockStmt p
  return (BLOCK_STMT a b)) <|>
  return BLOCK_END

blockStmt :: Parser r -> Parser (BLOCK_STMT r)
blockStmt p = blockStmtSep <|> return BLOCK_STMTEND
  where
    blockStmtSep =
      punctuation SEP_SEMICOLON >>
      (BLOCK_STMTSEP <$> block p)

-- We can convert the parse result to syntax as described in 'Goat.Lang.Class'

parseBlock
 :: Block_ r => (a -> Rhs (Item r)) -> BLOCK a -> r
parseBlock f b = fromList (toList b) where
  toList BLOCK_END = []
  toList (BLOCK_STMT a BLOCK_STMTEND) = [parseStmt f a]
  toList (BLOCK_STMT a (BLOCK_STMTSEP b)) =
    parseStmt f a : toList b

-- and show it as a grammatically valid string

showBlock :: ShowS -> (a -> ShowS) -> BLOCK a -> ShowS
showBlock wsep _sa BLOCK_END = wsep
showBlock wsep sa (BLOCK_STMT a b) =
  wsep .
  showStmt sa a .
  showBlockStmt wsep sa b

showBlockStmt :: ShowS -> (a -> ShowS) -> BLOCK_STMT a -> ShowS
showBlockStmt _wsep _sa BLOCK_STMTEND = id
showBlockStmt wsep sa (BLOCK_STMTSEP b) =
  showPunctuation SEP_SEMICOLON . showBlock wsep sa b

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
    STMT_PATH PATH (STMT_PATH a)
  | STMT_BLOCKDELIMEQ
      (PATTERNBLOCK PATTERN)
      (PATTERNBLOCKS PATTERN)
      a
data STMT_PATH a =
    STMT_PATHEND
  | STMT_PATHEQ (PATTERNBLOCKS PATTERN) a

proofStmt :: STMT a -> STMT a
proofStmt = parseStmt id

-- We can parse with

stmt :: Parser r -> Parser (STMT r)
stmt p = pathNext <|> blockNext where
  pathNext = do
    a <- path
    b <- stmtPath p
    return (STMT_PATH a b)
  blockNext = do
    punctuation LEFT_BRACE
    a <- patternBlock pattern
    punctuation RIGHT_BRACE
    b <- patternBlocks pattern
    symbol "="
    c <- p
    return (STMT_BLOCKDELIMEQ a b c)
  
  stmtPath :: Parser r -> Parser (STMT_PATH r)
  stmtPath p = (do
    a <- patternBlocks pattern
    symbol "="
    b <- p
    return (STMT_PATHEQ a b)) <|>
    return STMT_PATHEND

-- We can convert the parse result to syntax with

parseStmt
 :: Stmt_ r => (a -> Rhs r) -> STMT a -> r
parseStmt f = \case
  STMT_PATH a STMT_PATHEND -> 
    parsePath a
  
  STMT_PATH a (STMT_PATHEQ bs c) ->
    parsePattern (PATTERN_PATH a bs) #= f c
    
  STMT_BLOCKDELIMEQ a bs c ->
    parsePattern (PATTERN_BLOCKDELIM a bs) #= f c

-- and show the grammar as a string

showStmt :: (a -> ShowS) -> STMT a -> ShowS
showStmt _sa (STMT_PATH a STMT_PATHEND) =
  showPath a
showStmt sa (STMT_PATH a (STMT_PATHEQ bs c)) =
  showPattern (PATTERN_PATH a bs) .
  showSymbolSpaced (SYMBOL "=") .
  sa c
showStmt sa (STMT_BLOCKDELIMEQ a bs c) =
  showPattern (PATTERN_BLOCKDELIM a bs) .
  showSymbolSpaced (SYMBOL "=") .
  sa c

-- We need the following Goat syntax interfaces implemented for our grammar representation.

instance IsString (STMT a) where
  fromString s = STMT_PATH (fromString s) STMT_PATHEND

instance Select_ (STMT a) where
  type Selects (STMT a) = Either Self PATH
  type Key (STMT a) = IDENTIFIER
  c #. i = STMT_PATH (c #. i) STMT_PATHEND

instance Assign_ (STMT a) where
  type Lhs (STMT a) = PATTERN
  type Rhs (STMT a) = a
  PATTERN_PATH a b #= r = STMT_PATH a (STMT_PATHEQ b r)
  PATTERN_BLOCKDELIM a b #= r = STMT_BLOCKDELIMEQ a b r

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

newtype DEFINITION = DEFINITION (forall r . (OREXPR r -> r) -> r)
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
  EXPR_FIELD FIELD |
  EXPR_EXPRDELIM (OREXPR a)
data MODIFIERS a =
  MODIFIERS_START |
  MODIFIERS_SELECTOP (MODIFIERS a) IDENTIFIER |
  MODIFIERS_EXTENDDELIMOP (MODIFIERS a) (BLOCK a)

proofDefinition :: DEFINITION -> Either Self DEFINITION
proofDefinition = parseDefinition

-- To parse

definition :: Definition_ r => Parser r
definition = parseOrExpr id <$> orExpr definition

orExpr :: Parser r -> Parser (OREXPR r)
orExpr p = tokInfixR f (andExpr p) op where
  f a = EXPR_AND a EXPR_ANDEND
  op = symbol "||" $> \ a b -> EXPR_AND a (EXPR_OROP b)

andExpr :: Parser r -> Parser (ANDEXPR r)
andExpr p = tokInfixR f (compareExpr p) op where
  f a = EXPR_COMPARE a EXPR_COMPAREEND
  op = symbol "&&" $> \ a b -> EXPR_COMPARE a (EXPR_ANDOP b)

compareExpr :: Parser r -> Parser (COMPAREEXPR r)
compareExpr p = tokInfix f (sumExpr p) op where
  f a = EXPR_SUM a EXPR_SUMEND
  op =
    (symbol ">" $> mkOp EXPR_GTOP) <|>
    (symbol "<" $> mkOp EXPR_LTOP) <|>
    (symbol "==" $> mkOp EXPR_EQOP) <|>
    (symbol "!=" $> mkOp EXPR_NEOP) <|>
    (symbol ">=" $> mkOp EXPR_GEOP) <|>
    (symbol "<=" $> mkOp EXPR_LEOP)
  mkOp f a b = EXPR_SUM a (f b)

sumExpr :: Parser r -> Parser (SUMEXPR r)
sumExpr p = tokInfixL f (prodExpr p) op where
  f a = EXPR_PROD EXPR_SUMSTART a
  op = 
    (symbol "+" $> mkOp EXPR_ADDOP) <|>
    (symbol "-" $> mkOp EXPR_SUBOP)
  mkOp f a b = EXPR_PROD (f a) b

prodExpr :: Parser r -> Parser (PRODEXPR r)
prodExpr p = tokInfixL f (powExpr p) op where 
  f = EXPR_POW EXPR_PRODSTART
  op =
    (symbol "*" $> mkOp EXPR_MULOP) <|>
    (symbol "/" $> mkOp EXPR_DIVOP)
  mkOp f a b = EXPR_POW (f a) b

powExpr :: Parser r -> Parser (POWEXPR r)
powExpr p = tokInfixR f (unaryExpr p) op where
  f a = EXPR_UNARY a EXPR_UNARYEND
  op = symbol "^" $> \ a b -> EXPR_UNARY a (EXPR_POWOP b)

unaryExpr :: Parser r -> Parser (UNARYEXPR r)
unaryExpr p = (op <|> return EXPR_TERM) <*> term p where
  op =
   (symbol "-" $> EXPR_NEGOP) <|>
   (symbol "!" $> EXPR_NOTOP)

term :: Parser r -> Parser (TERM r)
term p = numberNext <|> originNext
  where
   numberNext = EXPR_NUMBER <$> numLiteral
   originNext = do
     a <- origin p
     b <- modifiers p
     return (EXPR_ORIGIN a b)

origin :: Parser r -> Parser (ORIGIN r)
origin p =
  (EXPR_TEXT <$> textLiteral) <|>
  (EXPR_IDENTIFIER <$> identifier) <|>
  (EXPR_FIELD <$> field) <|>
  blockNext <|>
  nestedNext
  where
    blockNext =
      EXPR_BLOCKDELIM <$>
      Parsec.between
        (punctuation LEFT_BRACE)
        (punctuation RIGHT_BRACE)
        (block p)
    nestedNext =
      EXPR_EXPRDELIM <$>
      Parsec.between
        (punctuation LEFT_PAREN)
        (punctuation RIGHT_PAREN)
        (orExpr p)

modifiers :: Parser r -> Parser (MODIFIERS r)
modifiers p = go MODIFIERS_START where
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
        (block p)
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
parseDefinition (DEFINITION f) = f (parseOrExpr id)

parseOrExpr :: Definition_ r => (a -> r) -> OREXPR a -> r
parseOrExpr k (EXPR_AND a EXPR_ANDEND) = parseAndExpr k a
parseOrExpr k (EXPR_AND a (EXPR_OROP b)) =
  parseAndExpr k a #|| parseOrExpr k b

parseAndExpr :: Definition_ r => (a -> r) -> ANDEXPR a -> r
parseAndExpr k (EXPR_COMPARE a EXPR_COMPAREEND) = 
  parseCompareExpr k a
parseAndExpr k (EXPR_COMPARE a (EXPR_ANDOP b)) =
  parseCompareExpr k a #&& parseAndExpr k b

parseCompareExpr
 :: Definition_ r => (a -> r) -> COMPAREEXPR a -> r
parseCompareExpr k (EXPR_SUM a b) =
  case b of
    EXPR_SUMEND -> parseSumExpr k a
    EXPR_EQOP b -> op (#==) a b
    EXPR_NEOP b -> op (#!=) a b
    EXPR_LTOP b -> op (#<) a b
    EXPR_LEOP b -> op (#<=) a b
    EXPR_GTOP b -> op (#>) a b
    EXPR_GEOP b -> op (#>=) a b
  where
    op f = f `on` parseSumExpr k

parseSumExpr :: Definition_ r => (a -> r) -> SUMEXPR a -> r
parseSumExpr k (EXPR_PROD a b) =
  case a of
    EXPR_SUMSTART -> parseProdExpr k b
    EXPR_ADDOP a -> op (+) a b
    EXPR_SUBOP a -> op (-) a b
  where
    op f a b = parseSumExpr k a `f` parseProdExpr k b

parseProdExpr :: Definition_ r => (a -> r) -> PRODEXPR a -> r
parseProdExpr k (EXPR_POW a b) =
  case a of
    EXPR_PRODSTART -> parsePowExpr k b
    EXPR_MULOP a -> op (*) a b
    EXPR_DIVOP a -> op (/) a b
  where
    op f a b = parseProdExpr k a `f` parsePowExpr k b

parsePowExpr :: Definition_ r => (a -> r) -> POWEXPR a -> r
parsePowExpr k (EXPR_UNARY a EXPR_UNARYEND) = parseUnaryExpr k a
parsePowExpr k (EXPR_UNARY a (EXPR_POWOP b)) =
  parseUnaryExpr k a #^ parsePowExpr k b

parseUnaryExpr :: Definition_ r => (a -> r) -> UNARYEXPR a -> r
parseUnaryExpr k (EXPR_NEGOP a) = neg_ (parseTerm k a)
parseUnaryExpr k (EXPR_NOTOP a) = not_ (parseTerm k a)
parseUnaryExpr k (EXPR_TERM a) = parseTerm k a

parseTerm :: Definition_ r => (a -> r) -> TERM a -> r
parseTerm _k (EXPR_NUMBER n) = parseNumLiteral n
parseTerm k (EXPR_ORIGIN a ms) = parseModifiers k a ms
  where
    parseModifiers
     :: Definition_ r => (a -> r) -> ORIGIN a -> MODIFIERS a -> r
    parseModifiers k a MODIFIERS_START = parseOrigin k a
    parseModifiers k a (MODIFIERS_SELECTOP ms i) =
      parseModifiers k a ms #. parseIdentifier i
    parseModifiers k a (MODIFIERS_EXTENDDELIMOP ms b) =
      parseModifiers k a ms # parseBlock k b

parseOrigin :: Definition_ r => (a -> r) -> ORIGIN a -> r
parseOrigin _k (EXPR_TEXT t) = parseTextLiteral t
parseOrigin k (EXPR_BLOCKDELIM b) = parseBlock k b
parseOrigin _k (EXPR_IDENTIFIER i) = parseIdentifier i
parseOrigin _k (EXPR_FIELD a) = parseField a
parseOrigin k (EXPR_EXPRDELIM e) = parseOrExpr k e

-- and for showing

showDefinition :: DEFINITION -> ShowS
showDefinition (DEFINITION f) = f (showOrExpr id)

showOrExpr :: (a -> ShowS) -> OREXPR a -> ShowS
showOrExpr sa (EXPR_AND a EXPR_ANDEND) = showAndExpr sa a
showOrExpr sa (EXPR_AND a (EXPR_OROP b)) =
  showAndExpr sa a .
  showSymbolSpaced (SYMBOL "||") .
  showOrExpr sa b

showAndExpr :: (a -> ShowS) -> ANDEXPR a -> ShowS
showAndExpr sa (EXPR_COMPARE a EXPR_COMPAREEND) =
  showCompareExpr sa a
showAndExpr sa (EXPR_COMPARE a (EXPR_ANDOP b)) =
  showCompareExpr sa a .
  showSymbolSpaced (SYMBOL "&&") .
  showAndExpr sa b

showCompareExpr :: (a -> ShowS) -> COMPAREEXPR a -> ShowS
showCompareExpr sa (EXPR_SUM a b) =
  case b of
    EXPR_SUMEND -> showSumExpr sa a
    EXPR_EQOP b -> op "==" a b
    EXPR_NEOP b -> op "!=" a b
    EXPR_LTOP b -> op "<" a b
    EXPR_LEOP b -> op "<=" a b
    EXPR_GTOP b -> op ">" a b
    EXPR_GEOP b -> op ">=" a b
  where
    op s a b =
      showSumExpr sa a .
      showSymbolSpaced (SYMBOL s) .
      showSumExpr sa b

showSumExpr :: (a -> ShowS) -> SUMEXPR a -> ShowS
showSumExpr sa (EXPR_PROD a b) = 
  case a of
    EXPR_SUMSTART -> showProdExpr sa b
    EXPR_ADDOP a -> op "+" a b
    EXPR_SUBOP a -> op "-" a b
  where
    op s a b =
      showSumExpr sa a .
      showSymbolSpaced (SYMBOL s) .
      showProdExpr sa b

showProdExpr :: (a -> ShowS) -> PRODEXPR a -> ShowS
showProdExpr sa (EXPR_POW a b) = 
  case a of
    EXPR_PRODSTART -> showPowExpr sa b
    EXPR_MULOP a -> op "*" a b
    EXPR_DIVOP a -> op "/" a b
  where
    op s a b =
      showProdExpr sa a .
      showSymbolSpaced (SYMBOL s) .
      showPowExpr sa b

showPowExpr :: (a -> ShowS) -> POWEXPR a -> ShowS
showPowExpr sa (EXPR_UNARY a EXPR_UNARYEND) = showUnaryExpr sa a
showPowExpr sa (EXPR_UNARY a (EXPR_POWOP b)) =
  showUnaryExpr sa a .
  showSymbolSpaced (SYMBOL "^") .
  showPowExpr sa b

showUnaryExpr :: (a -> ShowS) -> UNARYEXPR a -> ShowS
showUnaryExpr sa a =
  case a of
    EXPR_TERM a -> showTerm sa a
    EXPR_NEGOP a -> op "-" a
    EXPR_NOTOP a -> op "!" a
  where
    op s a =
      showSymbolSpaced (SYMBOL s) . 
      showTerm sa a

showTerm :: (a -> ShowS) -> TERM a -> ShowS
showTerm _sa (EXPR_NUMBER n) = showNumLiteral n
showTerm sa (EXPR_ORIGIN a b) =
  showOrigin sa a . showModifiers sa b

showOrigin :: (a -> ShowS) -> ORIGIN a -> ShowS
showOrigin _sa (EXPR_TEXT t) = showTextLiteral t
showOrigin sa (EXPR_BLOCKDELIM b) =
  showPunctuation LEFT_BRACE .
  showBlock (showString "\n    ") sa b .
  showPunctuation RIGHT_BRACE
showOrigin _sa (EXPR_IDENTIFIER i) = showIdentifier i
showOrigin _sa (EXPR_FIELD f) = showField f
showOrigin sa (EXPR_EXPRDELIM e) =
  showPunctuation LEFT_PAREN .
  showOrExpr sa e .
  showPunctuation RIGHT_PAREN

showModifiers :: (a -> ShowS) -> MODIFIERS a -> ShowS
showModifiers _sa MODIFIERS_START = id
showModifiers sa (MODIFIERS_SELECTOP ms i) =
  showModifiers sa ms .
  showSymbol (SYMBOL ".") .
  showIdentifier i
showModifiers sa (MODIFIERS_EXTENDDELIMOP ms b) =
  showModifiers sa ms .
  showPunctuation LEFT_BRACE .
  showBlock (showString "\n    ") sa b .
  showPunctuation RIGHT_BRACE

-- To implement the Goat syntax interface, 
-- we define a canonical expression representation.

data Canonical =
  Number NUMLITERAL |
  Text TEXTLITERAL |
  Block (BLOCK Canonical) |
  Local IDENTIFIER |
  Either Self Canonical :#. IDENTIFIER |
  Canonical :# BLOCK Canonical |
  Canonical :#|| Canonical | Canonical :#&& Canonical |
  Canonical :#== Canonical | Canonical :#!= Canonical |
  Canonical :#< Canonical | Canonical :#<= Canonical |
  Canonical :#> Canonical | Canonical :#>= Canonical |
  Canonical :#+ Canonical | Canonical :#- Canonical |
  Canonical :#* Canonical | Canonical :#/ Canonical |
  Canonical :#^ Canonical |
  Neg Canonical | Not Canonical

proofCanonical :: Canonical -> Either Self Canonical
proofCanonical = parseDefinition . toDefinition

-- and conversions

toDefinition :: Canonical -> DEFINITION
toDefinition a = DEFINITION f where
  f :: (OREXPR r -> r) -> r
  f kf = kf (toOrExpr tor a) where 
    tor c =
      case toDefinition c of DEFINITION f -> f kf

toOrExpr :: (Canonical -> r) -> Canonical -> OREXPR r
toOrExpr tor (a :#|| b) =
  EXPR_AND (toAndExpr tor a) (EXPR_OROP (toOrExpr tor b))
toOrExpr tor a = EXPR_AND (toAndExpr tor a) EXPR_ANDEND

toAndExpr :: (Canonical -> r) -> Canonical -> ANDEXPR r
toAndExpr tor (a :#&& b) =
  EXPR_COMPARE
    (toCompareExpr tor a)
    (EXPR_ANDOP (toAndExpr tor b))
toAndExpr tor a =
  EXPR_COMPARE (toCompareExpr tor a) EXPR_COMPAREEND

toCompareExpr :: (Canonical -> r) -> Canonical -> COMPAREEXPR r
toCompareExpr tor = \case
  a :#< b  -> op EXPR_LTOP a b
  a :#<= b -> op EXPR_LEOP a b
  a :#> b  -> op EXPR_GTOP a b
  a :#>= b -> op EXPR_GEOP a b
  a :#== b -> op EXPR_EQOP a b
  a :#!= b -> op EXPR_NEOP a b
  a        -> EXPR_SUM (toSumExpr tor a) EXPR_SUMEND
  where
    op f a b = EXPR_SUM (toSumExpr tor a) (f (toSumExpr tor b))

toSumExpr :: (Canonical -> r) -> Canonical -> SUMEXPR r
toSumExpr tor = \case
  a :#+ b -> op EXPR_ADDOP a b
  a :#- b -> op EXPR_SUBOP a b
  a       -> EXPR_PROD EXPR_SUMSTART (toProdExpr tor a)
  where
    op f a b = EXPR_PROD (f (toSumExpr tor a)) (toProdExpr tor b)

toProdExpr :: (Canonical -> r) -> Canonical -> PRODEXPR r
toProdExpr tor = \case
  a :#* b -> op EXPR_MULOP a b
  a :#/ b -> op EXPR_DIVOP a b
  a       -> EXPR_POW EXPR_PRODSTART (toPowExpr tor a)
  where
    op f a b = EXPR_POW (f (toProdExpr tor a)) (toPowExpr tor b)

toPowExpr :: (Canonical -> r) -> Canonical -> POWEXPR r
toPowExpr tor (a :#^ b) =
  EXPR_UNARY (toUnaryExpr tor a) (EXPR_POWOP (toPowExpr tor b))
toPowExpr tor a = EXPR_UNARY (toUnaryExpr tor a) EXPR_UNARYEND

toUnaryExpr :: (Canonical -> r) -> Canonical -> UNARYEXPR r
toUnaryExpr tor (Neg a) = EXPR_NEGOP (toTerm tor a)
toUnaryExpr tor (Not a) = EXPR_NOTOP (toTerm tor a)
toUnaryExpr tor a = EXPR_TERM (toTerm tor a)

toTerm :: (Canonical -> r) -> Canonical -> TERM r
toTerm _tor (Number n) = EXPR_NUMBER n
toTerm tor a = go tor a EXPR_ORIGIN
  where
    go
     :: (Canonical -> r)
     -> Canonical
     -> (ORIGIN r -> MODIFIERS r -> TERM r)
     -> TERM r
    go tor (Right a :#. i) k = go tor a k' where
      k' o ms = k o (ms `MODIFIERS_SELECTOP` i)
    
    go tor (a :# b) k = go tor a k' where  
      k' o ms =
        k o (ms `MODIFIERS_EXTENDDELIMOP` parseBlock tor b)
    
    go tor a k = k (toOrigin tor a) MODIFIERS_START

toOrigin
 :: (Canonical -> r) -> Canonical -> ORIGIN r
toOrigin _tor (Text t) = EXPR_TEXT t
toOrigin tor (Block b) = EXPR_BLOCKDELIM (parseBlock tor b)
toOrigin _tor (Local i) = EXPR_IDENTIFIER i
toOrigin _tor (Left Self :#. i) =
  EXPR_FIELD (FIELD_SELECTOP i)
toOrigin tor a = EXPR_EXPRDELIM (toOrExpr tor a)

-- Goat syntax interface implementation

instance IsString Canonical where
  fromString s = Local (fromString s)

instance IsString DEFINITION where
  fromString s = toDefinition (fromString s)

instance Select_ Canonical where
  type Selects Canonical = Either Self Canonical
  type Key Canonical = IDENTIFIER
  (#.) = (:#.)

instance Select_ DEFINITION where
  type Selects DEFINITION = Either Self DEFINITION
  type Key DEFINITION = IDENTIFIER
  a #. i = toDefinition (fmap fromDefinition a #. i)

instance Operator_ Canonical where
  (#||) = (:#||)
  (#&&) = (:#&&)
  (#==) = (:#==)
  (#!=) = (:#!=)
  (#>) = (:#>)
  (#>=) = (:#>=)
  (#<) = (:#<)
  (#<=) = (:#<=)
  (#+) = (:#+)
  (#-) = (:#-)
  (#*) = (:#*)
  (#/) = (:#/)
  (#^) = (:#^)
  not_ = Not
  neg_ = Neg

instance Operator_ DEFINITION where
  (#||) = toDefinition ... (#||) `on` fromDefinition
  (#&&) = toDefinition ... (#&&) `on` fromDefinition
  (#==) = toDefinition ... (#==) `on` fromDefinition
  (#!=) = toDefinition ... (#!=) `on` fromDefinition
  (#>) = toDefinition ... (#>) `on` fromDefinition
  (#>=) = toDefinition ... (#>=) `on` fromDefinition
  (#<) = toDefinition ... (#<) `on` fromDefinition
  (#<=) = toDefinition ... (#<=) `on` fromDefinition
  (#+) = toDefinition ... (#+) `on` fromDefinition
  (#-) = toDefinition ... (#-) `on` fromDefinition
  (#*) = toDefinition ... (#*) `on` fromDefinition
  (#/) = toDefinition ... (#/) `on` fromDefinition
  (#^) = toDefinition ... (#^) `on` fromDefinition
  not_ = toDefinition . not_ . fromDefinition
  neg_ = toDefinition . neg_ . fromDefinition

fromDefinition :: DEFINITION -> Canonical
fromDefinition = notSelf . parseDefinition

instance Extend_ Canonical where
  type Extension Canonical = BLOCK (Either Self Canonical)
  a # b = a :# parseBlock notSelf b

instance Extend_ DEFINITION where
  type Extension DEFINITION = BLOCK (Either Self DEFINITION)
  a # b = toDefinition (fromDefinition a # b') where
    b' =
      parseBlock (parseDefinition . notSelf) b

instance IsList Canonical where
  type Item Canonical = STMT (Either Self Canonical)
  fromList b = Block (parseBlock notSelf (fromList b))
  toList = error "IsList Canonical: toList"

instance IsList DEFINITION where
  type Item DEFINITION = STMT (Either Self DEFINITION)
  fromList b = toDefinition (Block b') where
    b' = 
      parseBlock (fromDefinition . notSelf) (fromList b)
  toList = error "IsList DEFINITION: toList"

instance TextLiteral_ Canonical where
  quote_ s = Text (quote_ s)

instance TextLiteral_ DEFINITION where
  quote_ s = toDefinition (quote_ s)

instance Num Canonical where
  fromInteger i = Number (fromInteger i)
  (+) = error "Num Canonical: (+)"
  (*) = error "Num Canonical: (*)"
  negate = error "Num Canonical: negate"
  abs = error "Num Canonical: abs"
  signum = error "Num Canonical: signum"

instance Num DEFINITION where
  fromInteger i = toDefinition (fromInteger i)
  (+) = error "Num DEFINITION: (+)"
  (*) = error "Num DEFINITION: (*)"
  negate = error "Num DEFINITION: negate"
  abs = error "Num DEFINITION: abs"
  signum = error "Num DEFINITION: signum"

instance Fractional Canonical where
  fromRational i = Number (fromRational i)
  (/) = error "Fractional Canonical: (/)"

instance Fractional DEFINITION where
  fromRational i = toDefinition (fromRational i)
  (/) = error "Fractional DEFINITION: (/)"
