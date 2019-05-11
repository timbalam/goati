> {-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, DeriveFunctor, LambdaCase #-}
> module Goat.Lang.Parser.Block where
> import Goat.Lang.Parser.Token
> import qualified Goat.Lang.Parser.Path as PATH
> import qualified Goat.Lang.Parser.Pattern as PATTERN
> import Goat.Lang.Class
> import Goat.Util ((...))
> import Control.Monad.Free (wrap, Free(..))
> import Data.Bifunctor (first)
> import Data.Function (on)
> import Data.Functor (($>))
> import Data.Void (Void)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))

Block
-----

A *BLOCK* is a sequence of *STMT*s separated and optionally terminated by literal semi-colons (';').
A source file will often consist of a single block.

    BLOCK := [STMT [';' BLOCK]]

We can represent a *BLOCK* as a concrete Haskell datatype.

> data BLOCK = BLOCK_END | BLOCK_STMT STMT BLOCK_STMT
> data BLOCK_STMT = BLOCK_STMTEND | BLOCK_STMTSEP BLOCK

and implement the 'Block_' Goat syntax interface (see 'Goat.Lang.Class')

> proofBlock :: BLOCK -> BLOCK
> proofBlock = parseBlock

To parse: 

> block :: Parser BLOCK
> block = (do
>   a <- stmt
>   b <- blockStmt
>   return (BLOCK_STMT a b)) <|>
>   return BLOCK_END

> blockStmt :: Parser BLOCK_STMT
> blockStmt = blockStmtSep <|> return BLOCK_STMTEND
>   where
>     blockStmtSep =
>       punctuation SEP_SEMICOLON >>
>       (BLOCK_STMTSEP <$> block)

We can convert the parse result to syntax as described in 'Goat.Lang.Class'

> parseBlock :: Block_ r => BLOCK -> r
> parseBlock b = fromList (toList b) where
>   toList BLOCK_END = []
>   toList (BLOCK_STMT a b) = case b of
>     BLOCK_STMTEND   -> [parseStmt a]
>
>     BLOCK_STMTSEP b -> parseStmt a : toList b

and show it as a grammatically valid string

> showBlock :: ShowS -> BLOCK -> ShowS
> showBlock wsep BLOCK_END = wsep
> showBlock wsep (BLOCK_STMT a b) =
>   wsep .
>   showStmt a .
>   showBlockStmt wsep b

> showBlockStmt :: ShowS -> BLOCK_STMT -> ShowS
> showBlockStmt _wsep BLOCK_STMTEND = id
> showBlockStmt wsep (BLOCK_STMTSEP b) =
>   showPunctuation SEP_SEMICOLON . showBlock wsep b

Implementing the Goat syntax interface

> instance IsList BLOCK where
>   type Item BLOCK = STMT
>   fromList [] = BLOCK_END
>   fromList (s:ss) =
>     BLOCK_STMT s (BLOCK_STMTSEP (fromList ss))
>   toList = error "IsList (Maybe BLOCK): toList"

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

A datatype concretely representing a *STMT*,
implementing the Goat syntax interface 'Stmt_',
is below.

> data STMT =
>     STMT_PATH PATH.PATH STMT_PATH
>   | STMT_BLOCKDELIMEQ
>       PATTERN.PATTERNBLOCK
>       PATTERN.PATTERNBLOCKS
>       DEFINITION
> data STMT_PATH =
>     STMT_PATHEND
>   | STMT_PATHEQ PATTERN.PATTERNBLOCKS DEFINITION

> proofStmt :: STMT -> STMT
> proofStmt = parseStmt

We can parse with

> stmt :: Parser STMT
> stmt = pathNext <|> blockNext where
>   pathNext = do
>     a <- PATH.path
>     b <- stmtPath
>     return (STMT_PATH a b)
>   blockNext = do
>     punctuation LEFT_BRACE
>     a <- PATTERN.patternBlock
>     punctuation RIGHT_BRACE
>     b <- PATTERN.patternBlocks
>     symbol "="
>     c <- definition
>     return (STMT_BLOCKDELIMEQ a b c)
>   
>   stmtPath :: Parser STMT_PATH
>   stmtPath = (do
>     a <- PATTERN.patternBlocks
>     symbol "="
>     b <- definition
>     return (STMT_PATHEQ a b)) <|>
>     return STMT_PATHEND

We can convert the parse result to syntax with

> parseStmt:: Stmt_ r => STMT -> r
> parseStmt = f where
>   f (STMT_PATH a STMT_PATHEND) = PATH.parsePath a
>   f (STMT_PATH a (STMT_PATHEQ b c)) =
>     PATTERN.parsePatternBlocks b (PATH.parsePath a)
>       #=
>         parseDefinition c
>   f (STMT_BLOCKDELIMEQ a b c) =
>     PATTERN.parsePatternBlocks
>       b
>       (PATTERN.parsePatternBlock a)
>       #=
>         parseDefinition c

and show the grammar as a string

> showStmt :: STMT -> ShowS
> showStmt (STMT_PATH a b) =
>   PATH.showPath a . showStmtPath b
> showStmt (STMT_BLOCKDELIMEQ a b c) =
>   showPunctuation LEFT_BRACE .
>   PATTERN.showPatternBlock (showChar ' ') a .
>   showPunctuation RIGHT_BRACE .
>   PATTERN.showPatternBlocks b .
>   showSymbolSpaced (SYMBOL "=") .
>   showDefinition c

> showStmtPath :: STMT_PATH -> ShowS
> showStmtPath STMT_PATHEND = id
> showStmtPath (STMT_PATHEQ a b) =
>   PATTERN.showPatternBlocks a .
>   showSymbolSpaced (SYMBOL "=") .
>   showDefinition b

We need the following Goat syntax interfaces implemented for our grammar representation.

> instance IsString STMT where
>   fromString s = STMT_PATH (fromString s) STMT_PATHEND

> instance Select_ STMT where
>   type Selects STMT = Either PATH.Self PATH.PATH
>   type Key STMT = IDENTIFIER
>   c #. i = STMT_PATH (c #. i) STMT_PATHEND

> instance Assign_ STMT where
>   type Lhs STMT = PATTERN.PATTERN
>   type Rhs STMT = DEFINITION
>   PATTERN.PATTERN_PATH a b #= r = STMT_PATH a (STMT_PATHEQ b r)
>   PATTERN.PATTERN_BLOCKDELIM a b #= r = STMT_BLOCKDELIMEQ a b r

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

Our concrete representation captures the associativity and 
precedence of the operators defined by  the Goat syntax interface.

> newtype DEFINITION = DEFINITION OREXPR
> data OREXPR = EXPR_AND ANDEXPR OREXPR_AND
> data OREXPR_AND = EXPR_ANDEND | EXPR_OROP OREXPR
> data ANDEXPR = EXPR_COMPARE COMPAREEXPR ANDEXPR_COMPARE
> data ANDEXPR_COMPARE =
>   EXPR_COMPAREEND | EXPR_ANDOP ANDEXPR
> data COMPAREEXPR = EXPR_SUM SUMEXPR COMPAREEXPR_SUM
> data COMPAREEXPR_SUM =
>   EXPR_SUMEND |
>   EXPR_EQOP SUMEXPR |
>   EXPR_NEOP SUMEXPR |
>   EXPR_LTOP SUMEXPR |
>   EXPR_LEOP SUMEXPR |
>   EXPR_GTOP SUMEXPR |
>   EXPR_GEOP SUMEXPR
> data SUMEXPR = EXPR_PROD SUMEXPR_SUM PRODEXPR
> data SUMEXPR_SUM =
>     EXPR_SUMSTART
>   | EXPR_ADDOP SUMEXPR
>   | EXPR_SUBOP SUMEXPR
> data PRODEXPR = EXPR_POW PRODEXPR_PROD POWEXPR
> data PRODEXPR_PROD =
>   EXPR_PRODSTART |
>   EXPR_MULOP PRODEXPR |
>   EXPR_DIVOP PRODEXPR
> data POWEXPR = EXPR_UNARY UNARYEXPR POWEXPR_UNARY
> data POWEXPR_UNARY =
>   EXPR_UNARYEND |
>   EXPR_POWOP POWEXPR
> data UNARYEXPR =
>   EXPR_TERM TERM |
>   EXPR_NEGOP TERM |
>   EXPR_NOTOP TERM
> data TERM =
>   EXPR_NUMBER NUMLITERAL |
>   EXPR_ORIGIN ORIGIN MODIFIERS
> data ORIGIN =
>   EXPR_TEXT TEXTLITERAL |
>   EXPR_BLOCKDELIM BLOCK |
>   EXPR_IDENTIFIER IDENTIFIER |
>   EXPR_FIELD PATH.FIELD |
>   EXPR_EXPRDELIM DEFINITION
> data MODIFIERS =
>   MODIFIERS_START |
>   MODIFIERS_SELECT MODIFIERS PATH.FIELD |
>   MODIFIERS_EXTENDDELIM MODIFIERS BLOCK

> proofDefinition :: DEFINITION -> DEFINITION
> proofDefinition = parseDefinition

To parse

> definition :: Parser DEFINITION
> definition = DEFINITION <$> orExpr

> orExpr :: Parser OREXPR
> orExpr = tokInfixR f andExpr op where
>   f a = EXPR_AND a EXPR_ANDEND
>   op = symbol "||" $> \ a b -> EXPR_AND a (EXPR_OROP b)

> andExpr :: Parser ANDEXPR
> andExpr = tokInfixR f compareExpr op where
>   f a = EXPR_COMPARE a EXPR_COMPAREEND
>   op = symbol "&&" $> \ a b -> EXPR_COMPARE a (EXPR_ANDOP b)

> compareExpr :: Parser COMPAREEXPR
> compareExpr = tokInfix f sumExpr op where
>   f a = EXPR_SUM a EXPR_SUMEND
>   op =
>     (symbol ">" $> mkOp EXPR_GTOP) <|>
>     (symbol "<" $> mkOp EXPR_LTOP) <|>
>     (symbol "==" $> mkOp EXPR_EQOP) <|>
>     (symbol "!=" $> mkOp EXPR_NEOP) <|>
>     (symbol ">=" $> mkOp EXPR_GEOP) <|>
>     (symbol "<=" $> mkOp EXPR_LEOP)
>   mkOp f a b = EXPR_SUM a (f b)

> sumExpr :: Parser SUMEXPR
> sumExpr = tokInfixL f prodExpr op where
>   f a = EXPR_PROD EXPR_SUMSTART a
>   op = 
>     (symbol "+" $> mkOp EXPR_ADDOP) <|>
>     (symbol "-" $> mkOp EXPR_SUBOP)
>   mkOp f a b = EXPR_PROD (f a) b

> prodExpr :: Parser PRODEXPR
> prodExpr = tokInfixL f powExpr op where 
>   f = EXPR_POW EXPR_PRODSTART
>   op =
>     (symbol "*" $> mkOp EXPR_MULOP) <|>
>     (symbol "/" $> mkOp EXPR_DIVOP)
>   mkOp f a b = EXPR_POW (f a) b

> powExpr :: Parser POWEXPR
> powExpr = tokInfixR f unaryExpr op where
>   f a = EXPR_UNARY a EXPR_UNARYEND
>   op = symbol "^" $> \ a b -> EXPR_UNARY a (EXPR_POWOP b)

> unaryExpr :: Parser UNARYEXPR
> unaryExpr = (op <|> return EXPR_TERM) <*> term where
>   op =
>    (symbol "-" $> EXPR_NEGOP) <|>
>    (symbol "!" $> EXPR_NOTOP)

> term :: Parser TERM
> term = numberNext <|> originNext
>   where
>    numberNext = EXPR_NUMBER <$> numLiteral
>    originNext = do
>      a <- origin
>      b <- modifiers
>      return (EXPR_ORIGIN a b)

> origin :: Parser ORIGIN
> origin =
>   (EXPR_TEXT <$> textLiteral) <|>
>   (EXPR_IDENTIFIER <$> identifier) <|>
>   (EXPR_FIELD <$> PATH.field) <|>
>   blockNext <|>
>   nestedNext
>   where
>     blockNext =
>       EXPR_BLOCKDELIM <$>
>       Parsec.between
>         (punctuation LEFT_BRACE)
>         (punctuation RIGHT_BRACE)
>         block
>     nestedNext =
>       EXPR_EXPRDELIM <$>
>       Parsec.between
>         (punctuation LEFT_PAREN)
>         (punctuation RIGHT_PAREN)
>         definition

> modifiers :: Parser MODIFIERS
> modifiers = go MODIFIERS_START where
>   go a = fieldNext a <|> blockNext a <|> return a
>   fieldNext a = do
>     f <- PATH.field
>     go (MODIFIERS_SELECT a f)
>   blockNext a = do
>     x <-
>       Parsec.between
>         (punctuation LEFT_BRACE)
>         (punctuation RIGHT_BRACE)
>         block
>     go (MODIFIERS_EXTENDDELIM a x)

> tokInfixR
>  :: (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
> tokInfixR f p op = do
>   a <- p
>   (do
>     s <- op
>     b <- tokInfixR f p op
>     return (s a b)) <|>
>     return (f a)

> tokInfix
>  :: (a -> b) -> Parser a -> Parser (a -> a -> b) -> Parser b
> tokInfix f p op = do
>   a <- p
>   (do
>      s <- op
>      b <- p
>      return (s a b)) <|>
>      return (f a)

> tokInfixL
>  :: (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
> tokInfixL f p op = do a <- p; rest (f a) where
>   rest a = (do
>     s <- op
>     b <- p
>     rest (s a b)) <|>
>     return a

For converting to syntax

> parseDefinition :: Definition_ r => DEFINITION -> r
> parseDefinition (DEFINITION a) = parseOrExpr a

> parseOrExpr :: Definition_ r => OREXPR -> r
> parseOrExpr (EXPR_AND a EXPR_ANDEND) = parseAndExpr a
> parseOrExpr (EXPR_AND a (EXPR_OROP b)) =
>   parseAndExpr a #|| parseOrExpr b

> parseAndExpr :: Definition_ r => ANDEXPR -> r
> parseAndExpr (EXPR_COMPARE a EXPR_COMPAREEND) = 
>   parseCompareExpr a
> parseAndExpr (EXPR_COMPARE a (EXPR_ANDOP b)) =
>   parseCompareExpr a #&& parseAndExpr b

> parseCompareExpr :: Definition_ r => COMPAREEXPR -> r
> parseCompareExpr (EXPR_SUM a b) =
>   case b of
>     EXPR_SUMEND -> parseSumExpr a
>     EXPR_EQOP b -> op (#==) a b
>     EXPR_NEOP b -> op (#!=) a b
>     EXPR_LTOP b -> op (#<) a b
>     EXPR_LEOP b -> op (#<=) a b
>     EXPR_GTOP b -> op (#>) a b
>     EXPR_GEOP b -> op (#>=) a b
>   where
>     op f = f `on` parseSumExpr

> parseSumExpr :: Definition_ r => SUMEXPR -> r
> parseSumExpr (EXPR_PROD a b) =
>   case a of
>     EXPR_SUMSTART -> parseProdExpr b
>     EXPR_ADDOP a -> op (+) a b
>     EXPR_SUBOP a -> op (-) a b
>   where
>     op f a b = parseSumExpr a `f` parseProdExpr b

> parseProdExpr :: Definition_ r => PRODEXPR -> r
> parseProdExpr (EXPR_POW a b) =
>   case a of
>     EXPR_PRODSTART -> parsePowExpr b
>     EXPR_MULOP a -> op (*) a b
>     EXPR_DIVOP a -> op (/) a b
>   where
>     op f a b = parseProdExpr a `f` parsePowExpr b

> parsePowExpr :: Definition_ r => POWEXPR -> r
> parsePowExpr (EXPR_UNARY a EXPR_UNARYEND) = parseUnaryExpr a
> parsePowExpr (EXPR_UNARY a (EXPR_POWOP b)) =
>   parseUnaryExpr a #^ parsePowExpr b

> parseUnaryExpr :: Definition_ r => UNARYEXPR -> r
> parseUnaryExpr (EXPR_NEGOP a) = neg_ (parseTerm a)
> parseUnaryExpr (EXPR_NOTOP a) = not_ (parseTerm a)
> parseUnaryExpr (EXPR_TERM a) = parseTerm a

> parseTerm :: Definition_ r => TERM -> r
> parseTerm (EXPR_NUMBER n) = parseNumLiteral n
> parseTerm (EXPR_ORIGIN a ms) = parseModifiers a ms
>   where
>     parseModifiers :: Definition_ r => ORIGIN -> MODIFIERS -> r
>     parseModifiers a MODIFIERS_START = parseOrigin a
>     parseModifiers a (MODIFIERS_SELECT ms f) =
>       PATH.selectField f (parseModifiers a ms)
>     parseModifiers a (MODIFIERS_EXTENDDELIM ms b) =
>       parseModifiers a ms # parseBlock b

> parseOrigin :: Definition_ r => ORIGIN -> r
> parseOrigin (EXPR_TEXT t) = parseTextLiteral t
> parseOrigin (EXPR_BLOCKDELIM b) = parseBlock b
> parseOrigin (EXPR_IDENTIFIER i) = parseIdentifier i
> parseOrigin (EXPR_FIELD a) = PATH.parseField a
> parseOrigin (EXPR_EXPRDELIM e) = parseDefinition e

and for showing

> showDefinition :: DEFINITION -> ShowS
> showDefinition (DEFINITION a) = showOrExpr a

> showOrExpr :: OREXPR -> ShowS
> showOrExpr (EXPR_AND a EXPR_ANDEND) = showAndExpr a
> showOrExpr (EXPR_AND a (EXPR_OROP b)) =
>   showAndExpr a .
>   showSymbolSpaced (SYMBOL "||") .
>   showOrExpr b

> showAndExpr :: ANDEXPR -> ShowS
> showAndExpr (EXPR_COMPARE a EXPR_COMPAREEND) =
>   showCompareExpr a
> showAndExpr (EXPR_COMPARE a (EXPR_ANDOP b)) =
>   showCompareExpr a .
>   showSymbolSpaced (SYMBOL "&&") .
>   showAndExpr b

> showCompareExpr :: COMPAREEXPR -> ShowS
> showCompareExpr (EXPR_SUM a b) =
>   case b of
>     EXPR_SUMEND -> showSumExpr a
>     EXPR_EQOP b -> op "==" a b
>     EXPR_NEOP b -> op "!=" a b
>     EXPR_LTOP b -> op "<" a b
>     EXPR_LEOP b -> op "<=" a b
>     EXPR_GTOP b -> op ">" a b
>     EXPR_GEOP b -> op ">=" a b
>   where
>     op s a b =
>       showSumExpr a .
>       showSymbolSpaced (SYMBOL s) .
>       showSumExpr b

> showSumExpr :: SUMEXPR -> ShowS
> showSumExpr (EXPR_PROD a b) = 
>   case a of
>     EXPR_SUMSTART -> showProdExpr b
>     EXPR_ADDOP a -> op "+" a b
>     EXPR_SUBOP a -> op "-" a b
>   where
>     op s a b =
>       showSumExpr a .
>       showSymbolSpaced (SYMBOL s) .
>       showProdExpr b

> showProdExpr :: PRODEXPR -> ShowS
> showProdExpr (EXPR_POW a b) = 
>   case a of
>     EXPR_PRODSTART -> showPowExpr b
>     EXPR_MULOP a -> op "*" a b
>     EXPR_DIVOP a -> op "/" a b
>   where
>     op s a b =
>       showProdExpr a .
>       showSymbolSpaced (SYMBOL s) .
>       showPowExpr b

> showPowExpr :: POWEXPR -> ShowS
> showPowExpr (EXPR_UNARY a EXPR_UNARYEND) = showUnaryExpr a
> showPowExpr (EXPR_UNARY a (EXPR_POWOP b)) =
>   showUnaryExpr a .
>   showSymbolSpaced (SYMBOL "^") .
>   showPowExpr b

> showUnaryExpr :: UNARYEXPR -> ShowS
> showUnaryExpr a =
>   case a of
>     EXPR_TERM a -> showTerm a
>     EXPR_NEGOP a -> op "-" a
>     EXPR_NOTOP a -> op "!" a
>   where
>     op s a =
>       showSymbolSpaced (SYMBOL s) . 
>       showTerm a

> showTerm :: TERM -> ShowS
> showTerm (EXPR_NUMBER n) = showNumLiteral n
> showTerm (EXPR_ORIGIN a b) = showOrigin a . showModifiers b

> showOrigin :: ORIGIN -> ShowS
> showOrigin (EXPR_TEXT t) = showTextLiteral t
> showOrigin (EXPR_BLOCKDELIM b) =
>   showPunctuation LEFT_BRACE .
>   showBlock (showString "\n    ") b .
>   showPunctuation RIGHT_BRACE
> showOrigin (EXPR_IDENTIFIER i) = showIdentifier i
> showOrigin (EXPR_FIELD f) = PATH.showField f
> showOrigin (EXPR_EXPRDELIM e) =
>   showPunctuation LEFT_PAREN .
>   showDefinition e .
>   showPunctuation RIGHT_PAREN

> showModifiers :: MODIFIERS -> ShowS
> showModifiers MODIFIERS_START = id
> showModifiers (MODIFIERS_SELECT ms f) =
>   showModifiers ms . PATH.showField f
> showModifiers (MODIFIERS_EXTENDDELIM ms b) =
>   showModifiers ms .
>   showPunctuation LEFT_BRACE .
>   showBlock (showString "\n    ") b .
>   showPunctuation RIGHT_BRACE

To implement the Goat syntax interface, 
we define a canonical expression representation.

> data Canonical a =
>   Number NUMLITERAL |
>   Text TEXTLITERAL |
>   Block BLOCK |
>   Local IDENTIFIER |
>   Either PATH.Self a :#. IDENTIFIER |
>   a :# BLOCK |
>   a :#|| a | a :#&& a | a :#== a | a :#!= a |
>   a :#< a | a :#<= a | a :#> a | a :#>= a | a :#+ a |
>   a :#- a | a :#* a | a :#/ a | a :#^ a |
>   Neg a | Not a
>   deriving Functor

> proofCanonical :: Free Canonical Void -> Free Canonical Void
> proofCanonical = parseDefinition . toDefinition

and conversions

> toDefinition :: Free Canonical Void -> DEFINITION
> toDefinition a = DEFINITION (toOrExpr a)

> toOrExpr :: Free Canonical Void -> OREXPR
> toOrExpr (Free (a :#|| b)) =
>   EXPR_AND (toAndExpr a) (EXPR_OROP (toOrExpr b))
> toOrExpr a = EXPR_AND (toAndExpr a) EXPR_ANDEND

> toAndExpr :: Free Canonical Void -> ANDEXPR
> toAndExpr (Free (a :#&& b)) =
>   EXPR_COMPARE (toCompareExpr a) (EXPR_ANDOP (toAndExpr b))
> toAndExpr a = EXPR_COMPARE (toCompareExpr a) EXPR_COMPAREEND

> toCompareExpr :: Free Canonical Void -> COMPAREEXPR
> toCompareExpr a =
>   case a of
>     Free (a :#< b)  -> op EXPR_LTOP a b
>     Free (a :#<= b) -> op EXPR_LEOP a b
>     Free (a :#> b)  -> op EXPR_GTOP a b
>     Free (a :#>= b) -> op EXPR_GEOP a b
>     Free (a :#== b) -> op EXPR_EQOP a b
>     Free (a :#!= b) -> op EXPR_NEOP a b
>     a               -> EXPR_SUM (toSumExpr a) EXPR_SUMEND
>    where
>      op f a b = EXPR_SUM (toSumExpr a) (f (toSumExpr b))

> toSumExpr :: Free Canonical Void -> SUMEXPR
> toSumExpr a =
>   case a of
>     Free (a :#+ b) -> op EXPR_ADDOP a b
>     Free (a :#- b) -> op EXPR_SUBOP a b
>     a              -> EXPR_PROD EXPR_SUMSTART (toProdExpr a)
>   where
>     op f a b = EXPR_PROD (f (toSumExpr a)) (toProdExpr b)

> toProdExpr :: Free Canonical Void -> PRODEXPR
> toProdExpr a =
>   case a of 
>     Free (a :#* b) -> op EXPR_MULOP a b
>     Free (a :#/ b) -> op EXPR_DIVOP a b
>     a              -> EXPR_POW EXPR_PRODSTART (toPowExpr a)
>   where
>     op f a b = EXPR_POW (f (toProdExpr a)) (toPowExpr b)

> toPowExpr :: Free Canonical Void -> POWEXPR
> toPowExpr (Free (a :#^ b)) =
>   EXPR_UNARY (toUnaryExpr a) (EXPR_POWOP (toPowExpr b))
> toPowExpr a = EXPR_UNARY (toUnaryExpr a) EXPR_UNARYEND

> toUnaryExpr :: Free Canonical Void -> UNARYEXPR
> toUnaryExpr (Free (Neg a)) = EXPR_NEGOP (toTerm a)
> toUnaryExpr (Free (Not a)) = EXPR_NOTOP (toTerm a)
> toUnaryExpr a = EXPR_TERM (toTerm a)

> toTerm :: Free Canonical Void -> TERM
> toTerm (Free (Number n)) = EXPR_NUMBER n
> toTerm a = go EXPR_ORIGIN a
>   where
>     go k (Free (Right a :#. i)) = go k' a where
>       k' o ms =
>         k o (MODIFIERS_SELECT ms (PATH.FIELD_SELECTOP i))
>
>     go k (Free (a :# x)) = go k' a where  
>       k' o ms = k o (MODIFIERS_EXTENDDELIM ms x)
>     
>     go k a = k (toOrigin a) MODIFIERS_START

> toOrigin :: Free Canonical Void -> ORIGIN
> toOrigin (Free (Text t)) = EXPR_TEXT t
> toOrigin (Free (Block b)) = EXPR_BLOCKDELIM b
> toOrigin (Free (Local i)) = EXPR_IDENTIFIER i
> toOrigin (Free (Left PATH.Self :#. i)) =
>   EXPR_FIELD (PATH.FIELD_SELECTOP i)
> toOrigin a = EXPR_EXPRDELIM (toDefinition a)

Goat syntax interface implementation

> instance IsString (Free Canonical a) where
>   fromString s = wrap (Local (fromString s))

> instance IsString DEFINITION where
>   fromString s = toDefinition (fromString s)

> instance Select_ (Free Canonical a) where
>   type Selects (Free Canonical a) =
>     Either PATH.Self (Free Canonical a)
>   type Key (Free Canonical a) = IDENTIFIER
>   a #. i = wrap (a :#. i)

> instance Select_ DEFINITION where
>  type Selects DEFINITION =
>    Either PATH.Self (Free Canonical Void)
>  type Key DEFINITION = IDENTIFIER
>  a #. i = toDefinition (a #. i)

> instance Operator_ (Free Canonical a) where
>   type Arg (Free Canonical a) = Free Canonical a
>   (#||) = wrap ... (:#||)
>   (#&&) = wrap ...(:#&&)
>   (#==) = wrap ... (:#==)
>   (#!=) = wrap ... (:#!=)
>   (#>) = wrap ... (:#>)
>   (#>=) = wrap ... (:#>=)
>   (#<) = wrap ... (:#<)
>   (#<=) = wrap ... (:#<=)
>   (#+) = wrap ... (:#+)
>   (#-) = wrap ... (:#-)
>   (#*) = wrap ... (:#*)
>   (#/) = wrap ... (:#/)
>   (#^) = wrap ... (:#^)
>   not_ = wrap . Not
>   neg_ = wrap . Neg

> instance Operator_ DEFINITION where
>   type Arg DEFINITION = Free Canonical Void
>   (#||) = toDefinition ... (#||)
>   (#&&) = toDefinition ... (#&&)
>   (#==) = toDefinition ... (#==)
>   (#!=) = toDefinition ... (#!=)
>   (#>) = toDefinition ... (#>)
>   (#>=) = toDefinition ... (#>=)
>   (#<) = toDefinition ... (#<)
>   (#<=) = toDefinition ... (#<=)
>   (#+) = toDefinition ... (#+)
>   (#-) = toDefinition ... (#-)
>   (#*) = toDefinition ... (#*)
>   (#/) = toDefinition ... (#/)
>   (#^) = toDefinition ... (#^)
>   not_ = toDefinition . not_
>   neg_ = toDefinition . neg_

> instance Extend_ (Free Canonical a) where
>   type Extends (Free Canonical a) = Free Canonical a
>   type Extension (Free Canonical a) = BLOCK
>   (#) = wrap ... (:#)

> instance Extend_ DEFINITION where
>   type Extends DEFINITION = Free Canonical Void
>   type Extension DEFINITION = BLOCK
>   a # b = toDefinition (a # b)

> instance IsList (Free Canonical a) where
>   type Item (Free Canonical a) = STMT
>   fromList b = wrap (Block (fromList b))
>   toList = error "IsList (Free Canonical a): toList"

> instance IsList DEFINITION where
>   type Item DEFINITION = STMT
>   fromList b = toDefinition (fromList b)
>   toList = error "IsList DEFINITION: toList"

> instance TextLiteral_ (Free Canonical a) where
>   quote_ s = wrap (Text (quote_ s))

> instance TextLiteral_ DEFINITION where
>   quote_ s = toDefinition (quote_ s)

> instance Num (Free Canonical a) where
>   fromInteger i = wrap (Number (fromInteger i))
>   (+) = error "Num (Free Canonical a): (+)"
>   (*) = error "Num (Free Canonical a): (*)"
>   negate = error "Num (Free Canonical a): negate"
>   abs = error "Num (Free Canonical a): abs"
>   signum = error "Num (Free Canonical a): signum"

> instance Num DEFINITION where
>   fromInteger i = toDefinition (fromInteger i)
>   (+) = error "Num DEFINITION: (+)"
>   (*) = error "Num DEFINITION: (*)"
>   negate = error "Num DEFINITION: negate"
>   abs = error "Num DEFINITION: abs"
>   signum = error "Num DEFINITION: signum"

> instance Fractional (Free Canonical a) where
>   fromRational i = wrap (Number (fromRational i))
>   (/) = error "Fractional (Free Canonical a): (/)"

> instance Fractional DEFINITION where
>   fromRational i = toDefinition (fromRational i)
>   (/) = error "Fractional DEFINITION: (/)"
