> {-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, DeriveFunctor #-}
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
> blockStmt = blockStmtSep <|> return BLOCKSTMT_END
>   where
>     blockStmtSep =
>       punctuation SEP_SEMICOLON >>
>       (BLOCK_STATMENTSEP <$> block)

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

> showBlockStmt :: ShowS -> BLOCK_STMTSEP -> ShowS
> showBlockStmt _wsep BLOCK_STMTEND = id
> showBlockStmt wsep (BLOCK_STMTSEP b) =
>   showPunctuation SEP_SEMICOLON . showBlock wsep b

Implementing the Goat syntax interface

> instance IsList BLOCK where
>   type Item BLOCK = STMT
>   fromList [] = BLOCK_END
>   fromList (s:ss) =
>     BLOCK_STMT s (BLOCK_STATMENTSEP (fromList ss))
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
>     PATTERN.parsePatternBlocks
>       b
>       (PATH.parsePath a) #=
>       parseDefinition c
>   f (STMT_BLOCKDELIMEQ a b c) =
>     PATTERN.parsePatternBlocks
>       b
>       (PATTERN.parsePatternBlock a) #=
>       parseDefinition b

and show the grammar as a string

> showStmt :: STMT -> ShowS
> showStmt (STMT_PATH a b) =
>   PATH.showPath a . showStmtPath b
> showStmt (STMT_BLOCKDELIMEQ a b c) =
>   showPunctuation LEFT_BRACE
>   PATTERN.showPatternBlock a .
>   showPunctuation RIGHT_BRACE .
>   PATTERN.showPatternBlocks b .
>   showSymbolSpaced (SYMBOL "=") .
>   showDefinition b

> showStmtPath :: STMT_PATH -> ShowS
> showStmtPath STMT_PATHEND = id
> showStmtPath (STMT_PATHEQ a b) =
>   PATTERN.showPatternBlocks a .
>   showSymbolSpaced (SYMBOL "=") .
>   showDefinition c

We need the following Goat syntax interfaces implemented for our grammar representation.

> instance IsString STMT where
>   fromString s = STMT_PATH (fromString s) STMT_PATHEND

> instance Select_ STMT where
>   type Compound STMT = Either PATH.Self PATH.PATH
>   type Key STMT = IDENTIFIER
>   c #. i = STMT_PATH (c #. i) STMT_PATHEND

> instance Assign_ STMT where
>   type Lhs STMT = PATTERN.PATTERN
>   type Rhs STMT = DEFINITION
>   PATTERN.PATTERN_PATH a b #= r = STMT_PATH a (STMT_PATHEQ b r)
>   PATTERN.PATTERN_BLOCK a b #= r = STMT_BLOCKDELIMEQ a b r

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
> data SUMEXPR = EXPR_PROD SUMEXPR_SUM PROD_EXPR
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
>   blockNext = do
>     x <-
>       Parsec.between
>         (punctuation LEFT_BRACE)
>         (punctuation RIGHT_BRACE)
>         block
>      go (MODIFIERS_EXTENDDELIM a x)

> tokInfixR
>  :: (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
> tokInfixR f p op = do
>   a <- p
>   (do
>     s <- op
>     b <- tokInfixR f p op
>     return (s a b))) <|>
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
> parseOrExpr (OREXPR a Nothing) = parseAndExpr a
> parseOrExpr (OREXPR a (Just (_, b))) =
>   parseAndExpr a #|| parseOrExpr b

> parseAndExpr :: Definition_ r => ANDEXPR -> r
> parseAndExpr (ANDEXPR a Nothing) = parseCompareExpr a
> parseAndExpr (ANDEXPR a (Just (_, b))) =
>   parseCompareExpr a #&& parseAndExpr b

> parseCompareExpr :: Definition_ r => COMPAREEXPR -> r
> parseCompareExpr (COMPAREEXPR a Nothing) = parseSumExpr a
> parseCompareExpr (COMPAREEXPR a (Just (b, c))) =
>   parseSumExpr a `op` parseSumExpr c
>   where
>     op = case b of
>       EQOP -> (#==)
>       NEOP -> (#!=)
>       LTOP -> (#<)
>       LEOP -> (#<=)
>       GTOP -> (#>)
>       GEOP -> (#>=)

> parseSumExpr :: Definition_ r => SUMEXPR -> r
> parseSumExpr (SUMEXPR Nothing a) = parseProdExpr a
> parseSumExpr (SUMEXPR (Just (c, b), a)) =
>   parseSumExpr c `op` parseProdExpr a
>   where
>     op = case b of ADDOP -> (+); SUBOP -> (-)

> parseProdExpr :: Definition_ r => PRODEXPR -> r
> parseProdExpr (PRODEXPR Nothing a) = parsePowExpr a
> parseProdExpr (PRODEXPR (Just (c, b)) a) =
>   parsePowExpr c `op` parseProdExpr a
>   where
>     op = case b of MULOP -> (*); DIVOP -> (/)

> parsePowExpr :: Definition_ r => POWEXPR -> r
> parsePowExpr (POWEXPR a Nothing) = parseUnaryExpr a
> parsePowExpr (POWEXPR a (Just (_, c))) =
>   parseUnaryExpr a #^ parsePowExpr c

> parseUnaryExpr :: Definition_ r => UNARYEXPR -> r
> parseUnaryExpr (UNARYEXPR (a, b)) = op (parseTerm b) where
>   op = case a of
>     Nothing    -> id
>     Just NEGOP -> neg_
>     Just NOTOP -> not_

> parseTerm :: Definition_ r => TERM -> r
> parseTerm (TERM_NUMBER n) = parseNumLiteral n
> parseTerm (EXPR_ORIGIN a b) =
>   parseModifiers b (parseOrigin a)

> parseOrigin :: Definition_ r => ORIGIN -> r
> parseOrigin (TERM_TEXT t) = quote_ t
> parseOrigin (TERM_BLOCK _ b _) = parseBlock b
> parseOrigin (TERM_IDENTIFIER i) = parseIdentifier i
> parseOrigin (TERM_FIELD a) = PATH.parseField a
> parseOrigin (TERM_NESTED _ b _) = parseDefinition b

> parseModifiers :: Definition_ r => MODIFIERS -> r -> r
> parseModifiers (OP_SELECT (PATH.FIELD (_, i))) a =
>  a #. parseIdentifier i
> parseModifiers (OP_EXTEND _ b _) a = a # parseBlock b

and for showing

> showDefinition :: DEFINITION -> ShowS
> showDefinition (DEFINITION a) = showOrExpr a

> showOrExpr :: OREXPR -> ShowS
> showOrExpr (OREXPR (a, b)) = showAndExpr a .
>   maybe id (\ (a, b) -> showOrOp a . showOrExpr b) b

> showOrOp :: OROP -> ShowS
> showOrOp OROP = showSymbolSpaced (SYMBOL "||")

> showAndExpr :: ANDEXPR -> ShowS
> showAndExpr (ANDEXPR (a, b)) = showCompareExpr a .
>   maybe id (\(a, b) -> showAndOp a . showAndExpr b) b

> showAndOp :: ANDOP -> ShowS
> showAndOp ANDOP = showSymbolSpaced (SYMBOL "&&")

> showCompareExpr :: COMPAREEXPR -> ShowS
> showCompareExpr (COMPAREEXPR (a, b)) = showSumExpr a .
>   maybe id (\ (a, b) -> showCompareOp a . showSumExpr b) b

> showCompareOp :: COMPAREOP -> ShowS
> showCompareOp a = showSymbolSpaced (SYMBOL s) where
>   s = case a of
>     EQOP -> "=="
>     NEOP -> "!="
>     LTOP -> "<"
>     LEOP -> "<="
>     GTOP -> ">"
>     GEOP -> ">="

> showSumExpr :: SUMEXPR -> ShowS
> showSumExpr (SUMEXPR (a, b)) = 
>   maybe id (\ (a, b) -> showSumExpr a . showSumOp b) a .
>   showProdExpr b

> showSumOp :: SUMOP -> ShowS
> showSumOp a = showSymbolSpaced (SYMBOL s) where
>   s = case a of ADDOP -> "+"; SUBOP -> "-"

> showProdExpr :: PRODEXPR -> ShowS
> showProdExpr (PRODEXPR (a, b)) = maybe id (\ (a, b) -> 
>   showProdExpr a . showProdOp b) a . showPowExpr b

> showProdOp :: PRODOP -> ShowS
> showProdOp a = showSymbolSpaced (SYMBOL s) where
>   s = case a of MULOP -> "*"; DIVOP -> "/"

> showPowExpr :: POWEXPR -> ShowS
> showPowExpr (POWEXPR (a, b)) = showUnaryExpr a .
>   maybe id (\ (a, b) -> showPowOp a . showPowExpr b) b

> showPowOp :: POWOP -> ShowS
> showPowOp POWOP = showSymbolSpaced (SYMBOL "^")

> showUnaryExpr :: UNARYEXPR -> ShowS
> showUnaryExpr (UNARYEXPR (a, b)) = maybe id showUnaryOp a . 
>   showTerm b

> showUnaryOp :: UNARYOP -> ShowS
> showUnaryOp a = showSymbolSpaced (SYMBOL s) where
>   s = case a of NEGOP -> "-"; NOTOP -> "!"

> showTerm :: TERM -> ShowS
> showTerm (TERM_NUMBER n) = showNumLiteral n
> showTerm (EXPR_ORIGIN a b) = showOrigin a . showModifiers b

> showOrigin :: ORIGIN -> ShowS
> showOrigin (TERM_TEXT t) = showTextLiteral t
> showOrigin (TERM_BLOCK a b c) =
>   showExprDelimLeft a . maybe id showBlock b .
>   showExprDelimRight c
> showOrigin (TERM_IDENTIFIER i) = showIdentifier i
> showOrigin (TERM_FIELD f) = PATH.showField f
> showOrigin (TERM_NESTED a b c) = showExprDelimLeft a .
>   showDefinition b . showExprDelimRight c

> showModifiers :: MODIFIERS -> ShowS
> showModifiers (MODIFIERS (a, b)) = showModifier a .
>   maybe id showModifiers b

> showModifier :: MODIFIER -> ShowS
> showModifier (OP_SELECT f) = PATH.showField f
> showModifier (OP_EXTEND a b c) = showBlockDelimLeft a .
>   maybe id showBlock b . showBlockDelimRight b

> showExprDelimLeft :: EXPRDELIMLEFT -> ShowS
> showExprDelimLeft EXPRDELIMLEFT = showPunctuation LEFT_PAREN

> showExprDelimRight :: EXPRDELIMRIGHT -> ShowS
> showExprDelimRight EXPRDELIMRIGHT = showPunctuation RIGHT_PAREN

> showBlockDelimLeft :: BLOCKDELIMLEFT -> ShowS
> showBlockDelimLeft BLOCKDELIMLEFT = showPunctuation LEFT_BRACE

> showBlockDelimRight :: BLOCKDELIMRIGHT -> ShowS
> showBlockDelimRight BLOCKDELIMRIGHT =
>   showPunctuation RIGHT_BRACE

To implement the Goat syntax interface, 
we define a canonical expression representation.

> data Canonical a =
>   Number NUMLITERAL |
>   Text TEXTLITERAL |
>   Block (Maybe BLOCK) |
>   Local IDENTIFIER |
>   Either PATH.Self a :#. IDENTIFIER |
>   a :# Maybe BLOCK |
>   a :#|| a | a :#&& a | a :#== a | a :#!= a |
>   a :#< a | a :#<= a | a :#> a | a :#>= a | a :#+ a |
>   a :#- a | a :#* a | a :#/ a | a :#^ a |
>   Neg a | Not a
>   deriving Functor

and conversions

> toDefinition :: Free Canonical Void -> DEFINITION
> toDefinition a = DEFINITION (toOrExpr a)

> toOrExpr :: Free Canonical Void -> OREXPR
> toOrExpr (Free (a :#|| b)) =
>   OREXPR (toAndExpr a, Just (OROP, toOrExpr b))
> toOrExpr a = OREXPR (toAndExpr a, Nothing)

> toAndExpr :: Free Canonical Void -> ANDEXPR
> toAndExpr (Free (a :#&& b)) = ANDEXPR
>   (toCompareExpr a, Just (ANDOP, toAndExpr b))
> toAndExpr a = ANDEXPR (toCompareExpr a, Nothing)

> toCompareExpr :: Free Canonical Void -> COMPAREEXPR
> toCompareExpr = f where
>  f (Free (a :#< b)) = op a LTOP b
>  f (Free (a :#<= b)) = op a LEOP b
>  f (Free (a :#> b)) = op a GTOP b
>  f (Free (a :#>= b)) = op a GEOP b
>  f (Free (a :#== b)) = op a EQOP b
>  f (Free (a :#!= b)) = op a NEOP
>  f a = COMPAREEXPR (toSumExpr a, Nothing)
>  op a b c = COMPAREEXPR
>   (toSumExpr a, Just (b, toSumExpr c))

> toSumExpr :: Free Canonical Void -> SUMEXPR
> toSumExpr = f where
>   f (Free (a :#+ b)) = op a ADDOP b
>   f (Free (a :#- b)) = op a SUBOP b
>   f a = SUMEXPR (Nothing, toProdExpr a)
>   op a b c = SUMEXPR (Just (toSumExpr a, b), toProdExpr c)

> toProdExpr :: Free Canonical Void -> PRODEXPR
> toProdExpr = f where
>   f (Free (a :#* b)) = op a MULOP b
>   f (Free (a :#/ b)) = op a DIVOP b
>   f a = PRODEXPR (Nothing, toPowExpr a)
>   op a b c =
>     PRODEXPR (Just (toProdExpr a, b)) (toPowExpr c)

> toPowExpr :: Free Canonical Void -> POWEXPR
> toPowExpr (Free (a :#^ b)) =
>   PRODEXPR (toUnaryExpr a) (Just (POWOP, toPowExpr b))
> toPowExpr a = POWEXPR (toUnaryExpr a) Nothing

> toUnaryExpr :: Free Canonical Void -> UNARYEXPR
> toUnaryExpr = f where
>   f (Free (Neg a)) = op NEGOP a
>   f (Free (Not a)) = op NOTOP a
>   f a = UNARYEXPR Nothing (toTerm a)
>   op a b = UNARYEXPR (Just a) (toTerm b)

> toTerm :: Free Canonical Void -> TERM
> toTerm (Free (Number n)) = TERM_NUMBER n
> toTerm a = go a id where
>   go (Free (Right a :#. i)) k = go a k' where
>     k' a = Just (k a `modifies` f)
>     f = OP_SELECT (Left PATH.Self #. i)
>   go (Free (a :# x)) k = go a k' where
>     k' a = Just (k a `modifies` x')
>     x' = OP_EXTEND BLOCKDELIMLEFT x BLOCKDELIMRIGHT
>   go a k = EXPR_ORIGIN (toOrigin a) (k Nothing)

> modifies :: Maybe MODIFIERS -> MODIFIER -> MODIFIERS
> modifies Nothing c = MODIFIERS c Nothing
> modifies (Just (MODIFIERS a b)) c =
>   MODIFIERS a (Just (modifies b c))

> toOrigin :: Free Canonical Void -> ORIGIN
> toOrigin (Free (Text t)) = TERM_TEXT t
> toOrigin (Free (Block b)) =
>   TERM_BLOCK BLOCKDELIMLEFT b BLOCKDELIMRIGHT
> toOrigin (Free (Local i)) = TERM_IDENTIFIER i
> toOrigin (Free (Left PATH.Self :#. i)) =
>   TERM_FIELD (Left PATH.Self #. i)
> toOrigin a =
>   TERM_NESTED EXPRDELIMLEFT (toDefinition a) EXPRDELIMRIGHT

Goat syntax interface implementation

> instance IsString (Free Canonical a) where
>   fromString s = wrap (Local (fromString s))

> instance IsString DEFINITION where
>   fromString s = toDefinition (fromString s)

> instance Select_ (Free Canonical a) where
>   type Compound (Free Canonical a) =
>     Either PATH.Self (Free Canonical a)
>   type Key (Free Canonical a) = IDENTIFIER
>   a #. i = wrap (a :#. i)

> instance Select_ DEFINITION where
>  type Compound DEFINITION = Either PATH.Self DEFINITION
>  type Key DEFINITION = IDENTIFIER
>  a #. i = toDefinition (fmap parseDefinition a #. i)

> instance Operator_ (Free Canonical a) where
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
>   (#||) = toDefinition ... (#||) `on` parseDefinition
>   (#&&) = toDefinition ... (#&&) `on` parseDefinition
>   (#==) = toDefinition ... (#==) `on` parseDefinition
>   (#!=) = toDefinition ... (#!=) `on` parseDefinition
>   (#>) = toDefinition ... (#>) `on` parseDefinition
>   (#>=) = toDefinition ... (#>=) `on` parseDefinition
>   (#<) = toDefinition ... (#<) `on` parseDefinition
>   (#<=) = toDefinition ... (#<=) `on` parseDefinition
>   (#+) = toDefinition ... (#+) `on` parseDefinition
>   (#-) = toDefinition ... (#-) `on` parseDefinition
>   (#*) = toDefinition ... (#*) `on` parseDefinition
>   (#/) = toDefinition ... (#/) `on` parseDefinition
>   (#^) = toDefinition ... (#^) `on` parseDefinition
>   not_ = toDefinition . not_ . parseDefinition
>   neg_ = toDefinition . neg_ . parseDefinition

> instance Extend_ (Free Canonical a) where
>   type Extension (Free Canonical a) = Maybe BLOCK
>   (#) = wrap ... (:#)

> instance Extend_ DEFINITION where
>   type Extension DEFINITION = Maybe BLOCK
>   a # b  = toDefinition (parseDefinition a # b)

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
