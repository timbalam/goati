> {-# LANGUAGE TypeFamilies #-}
> module Goat.Lang.Parser.Block where
> import Goat.Lang.Parser.Token
> import qualified Goat.Lang.Parser.Path as PATH
> import qualified Goat.Lang.Parser.Pattern as PATTERN
> import Goat.Lang.Class
> import Goat.Util ((...))
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))

Block
-----

A *BLOCK* is a sequence of *STATEMENT*s separated and optionally terminated by literal semi-colons (';').
A source file will often consist of a single block.

    BLOCK := STATEMENT [';' [BLOCK]]

We can represent a *BLOCK* as a concrete Haskell datatype.

> newtype BLOCK = BLOCK (STATEMENT, Maybe (BLOCKSEP, Maybe BLOCK))
> data BLOCKSEP = BLOCKSEP

and implement the 'Block_' Goat syntax interface (see 'Goat.Lang.Class')

> proofBlock :: Maybe BLOCK -> Maybe BLOCK
> proofBlock = parseBlock

To parse: 

> block :: Parser BLOCK
> block = do
>   a <- statement
>   b <- Parsec.optionMaybe 
>     (do
>       a <- blockSep
>       b <- Parsec.optionMaybe block
>       return (a, b))
>   return (Block (a, b))

> blockSep :: Parser BLOCKSEP
> blockSep = punctuation SEP_SEMICOLON $> BLOCKSEP

We can convert the parse result to syntax as described in 'Goat.Lang.Class'

> parseBlock :: Block_ r => Maybe BLOCK -> r
> parseBlock b = fromList (maybe [] list b) where
>   list (Block (a, b)) =
>     parseStatement a : maybe [] (maybe [] list) b

and show it as a grammatically valid string

> showBlock :: ShowS -> BLOCK -> ShowS
> showBlock wsep (Block (a, b)) =
>   wsep . showStatement a . maybe id (\ (a, b) ->
>     showBlockSep a . maybe id (showBlock wsep) b) b

> showBlockSep :: BLOCKSEP -> ShowS
> showBlockSep BLOCKSEP = showPunctuation SEP_SEMICOLON

Implementing the Goat syntax interface

> instance IsList (Maybe BLOCK) where
>   type Item (Maybe BLOCK) = STATEMENT
>   fromList [] = Nothing
>   fromList (s:ss) =
>     Just (Block (s, Just (BLOCKSEP, fromList ss)))
>   toList = errorWithoutStackTrace "IsList (Maybe BLOCK): toList"

Statement
---------

In terms of Goat's grammar a *STATEMENT* can have a few forms.
The first form starts with a *PATH*,
and can optionally be continued by a *PATTERNBLOCKS*, an equals sign ('='), and a *DEFINITION*,
or alternatively by an equals sign ('=') and a *DEFINITION*.
The second form starts with *PATTERNBLOCKS*,
and finishes with an equals sign ('=') and a *DEFINITION*.

    STATEMENT :=
        PATH [[PATTERNBLOCKS] '=' DEFINITION]
      | PATTERNBLOCKS '=' DEFINITION

A datatype concretely representing a *STATEMENT*,
implementing the Goat syntax interface 'Statement_',
is below.

> newtype STATEMENT =
>   STATEMENT_PATH
>     (PATH.PATH, Maybe (Maybe PATTERN.PATTERNBLOCKS,
>       STATEMENTEQ, DEFINITION)) |
>   STATEMENT_BLOCK
>     (PATTERN.PATTERNBLOCKS, STATEMENTEQ, DEFINITION)
> data STATEMENTEQ = STATEMENTEQ

> proofStatement :: STATEMENT -> STATEMENT
> proofStatement = parseStatement

We can parse with

> statement :: Parser STATEMENT
> statement = pathFirst <|> blockFirst where
>   pathFirst = do
>     a <- PATH.path
>     b <- Parsec.optionMaybe 
>       (do
>         a <- Parsec.optionMaybe PATTERN.patternBlocks
>         b <- statementeq
>         c <- definition
>         return (a, b, c))
>     return (STATEMENT_PATH (a, b))
>   blockFirst = do
>     a <- PATTERN.patternBlocks
>     b <- statementeq
>     c <- definition
>     return (STATEMENT_BLOCK (a, b, c))

> statementeq :: Parser STATEMENTEQ
> statementeq = symbol "=" $> STATEMENTEQ

We can convert the parse result to syntax with

> parseStatement:: Statement_ r => STATEMENT -> r
> parseStatement = f where
>   f (STATEMENT_PATH (a, Nothing)) = PATH.parsePath a
>   f (STATEMENT_PATH (a, Just (b, _, c))) =
>     PATTERN.parseExtendPatternBlocks b (PATH.parsePath a) #=
>     parseDefinition c
>   f (STATEMENT_BLOCK (a, _, b)) =
>     PATTERN.parsePatternBlocks a #= parseDefinition b

and show the grammar as a string

> showStatement :: STATEMENT -> ShowS
> showStatement (STATEMENT_PATH (a, b)) =
>   PATH.showPath a . maybe id (\ (b, c, d) ->
>     maybe id PATH.showPatternBlocks b .
>     showStatementEq c . showDefinition d) b
> showStatement (STATEMENT_BLOCK (a, b, c)) =
>   PATH.showPatternBlocks a . showStatementEq b .
>   showDefinition c

> showStatementEq :: STATEMENTEQ -> ShowS
> showStatementEq STATEMENTEQ =
>   showChar ' ' . showSymbolSpaced (SYMBOL "=") . showChar ' '

We need the following Goat syntax interfaces implemented for our grammar representation.

> instance IsString STATEMENT where
>   fromString s = STATEMENT_PATH (fromString s, Nothing)

> instance Select_ STATEMENT where
>   type Compound STATEMENT = (Either PATH.PATH PATH.Self)
>   type Key STATEMENT = IDENTIFIER
>   c #. i = STATEMENT_PATH (c #. i, Nothing)

> instance Assign_ STATEMENT where
>   type Lhs STATEMENT = PATTERN.PATTERN
>   type Rhs STATEMENT = DEFINITION
>   PATTERN_PATH (a, b) #= c = STATEMENT_PATH
>     (a, Just (b, STATEMENTEQ, c))
>   PATTERN_BLOCK (a, b) #= c = STATEMENT_BLOCK
>     (a, STATEMENTEQ, b)

Definition
----------

A *DEFINITION* is an *OREXPR*.
An *OREXPR* is a non-empty sequence of *ANDEXPR*s,
separated by double-bars ('||').
An *ANDEXPR* is a non-empty sequence of *COMPAREEXPR*s,
separated by double-and signs ('&&').
A *COMPAREEXPR* is a *POWEREXPR*,
optionally followed by a *COMPAREOP* and a *SUMEXPR*.
A *COMPAREOP* is either a double-equal sign ('=='),
an exclamation mark and equal sign ('!='),
a less-than sign ('<'),
a less-than sign and equal sign ('<='),
a greater-than sign ('>'),
or a greater-than sign and equal sign ('>=').
A *SUMEXPR* is a non-empty sequence of *PRODUCTEXPR*s,
separated by *SUMOP*s.
A *SUMOP* is a plus sign ('+') or minus sign ('-').
A *PRODUCTEXPR* is a non-empty sequence of *POWEREXPR*s,
separated by *PRODUCTOP*s.
A *PRODUCTOP* is either an asterisk ('*') or a slash ('/').
A *POWEREXPR* is a non-empty sequence of *UNARYEXPR*s,
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
    SUMEXPR := PRODUCTEXPR [SUMOP SUMEXPR]
    SUMOP := '+' | '-'
    PRODUCTEXPR := POWEREXPR [PRODUCTOP PRODUCTEXPR]
    PRODUCTOP := '*' | '/'
    POWEREXPR := UNARYEXPR ['^' POWEREXPR]
    UNARYEXPR := [UNARYOP] TERM
    UNARYOP := '-' | '!'
    TERM := NUMBERLITERAL | FIELDEXPR
    FIELDEXPR := ORIGIN [MODIFIERS]
    ORIGIN :=
        TEXTLITERAL
      | IDENTIFIER
      | FIELD
      | '{' BLOCK '}'
      | '(' DEFINITION ')'
    MODIFIERS := MODIFIER [MODIFIERS]
    MODIFIER := FIELD | '{' BLOCK '}'

Our concrete representation captures the associativity and 
precedence of the operators defined by  the Goat syntax interface.
    
> newtype DEFINITION = DEFINITION OREXPR
> data OREXPR = OREXPR ANDEXPR Maybe (OROP, OREXPR)
> data OROP = OROP
> data ANDEXPR = ANDEXPR COMPAREEXPR (Maybe (ANDOP, ANDEXPR))
> data ANDOP = ANDOP
> data COMPAREEXPR =
>   COMPAREEXPR SUMEXPR (Maybe (COMPAREOP, SUMEXPR))
> data COMPAREOP = EQOP | NEOP | LTOP | LEOP | GTOP | GEOP
> data SUMEXPR = SUMEXPR (Maybe (SUMEXPR, SUMOP)) PRODUCTEXPR
> data SUMOP = ADDOP | SUBOP
> data PRODUCTEXPR = PRODUCTEXPR
>   (Maybe (PRODUCTEXPR, PRODUCTOP)) POWEREXPR
> data PRODUCTOP = MULOP | DIVOP
> data POWEREXPR = POWEREXPR UNARYEXPR (Maybe (POWOP, POWEREXPR))
> data POWOP = POWOP
> data UNARYEXPR = UNARYEXPR (Maybe UNARYOP) TERM
> data UNARYOP = NEGOP | NOTOP
> data TERM = EXPR_NUMBER NUMBERLITERAL | TERM_FIELD FIELDEXPR
> data FIELDEXPR = FIELDEXPR ORIGIN (Maybe MODIFIERS)
> data ORIGIN = EXPR_TEXT TEXTLITERAL |
>   EXPR_BLOCK BLOCKDELIMLEFT (Maybe BLOCK) BLOCKDELIMRIGHT |
>   EXPR_IDENTIFIER IDENTIFIER |
>   EXPR_FIELD FIELD |
>   EXPR_NESTED EXPRDELIMLEFT DEFINITION EXPRDELIMRIGHT
> data MODIFIERS = MODIFIERS MODIFIER (Maybe MODIFIERS)
> data MODIFIER = OP_SELECT PATH.FIELD |
>   OP_EXTEND BLOCKDELIMLEFT (Maybe BLOCK) BLOCKDELIMRIGHT
> data EXPRDELIMLEFT = EXPRDELIMLEFT
> data EXPRDELIMRIGHT = EXPRDELIMRIGHT
> data BLOCKDELIMLEFT = BLOCKDELIMLEFT
> data BLOCKDELIMRIGHT = BLOCKDELIMRIGHT

> proofDefinition :: DEFINITION -> DEFINITION
> proofDefinition = parseDefinition

To parse

> definition :: Parser DEFINITION
> definition = DEFINITION <$> orExpr

> orExpr :: Parser OREXPR
> orExpr = tokInfixR OREXPR andExpr orOp

> orOp :: Parser OROP
> orOp = symbol "||" $> OROP

> andExpr :: Parser ANDEXPR
> andExpr = tokInfixR ANDEXPR compareExpr andOp

> andOp :: Parser ANDOP
> andOp = symbol "&&" $> ANDOP

> compareExpr :: Parser COMPAREEXPR
> compareExpr = tokInfix COMPAREEXPR sumExpr comparisonOp

> compareOp :: Parser COMPAREOP
> compareOp = (symbol ">" &> return GTOP) <|>
>   (symbol "<" >> return LTOP) <|>
>   (symbol "==" >> return EQOP) <|>
>   (symbol "!=" >> return NEOP) <|>
>   (symbol ">=" >> return GEOP) <|>
>   (symbol "<=" >> return LEOP)

> sumExpr :: Parser SUMEXPR
> sumExpr = tokInfixL SUMEXPR productExpr sumOp

> sumOp :: Parser SUMOP
> sumOp = (symbol "+" >> return ADDOP) <|>
>   (symbol "-" >> return SUBOP)

> productExpr :: Parser PRODUCTEXPR
> productExpr = tokInfixL PRODUCTEXPR powerExpr productOp 

> productOp :: Parser PRODUCTOP
> productOp = (symbol "*" >> return MULOP) <|>
>   (symbol "/" >> return DIVOP)

> powerExpr :: Parser POWEREXPR
> powerExpr = tokInfixR POWEREXPR unaryExpr powOp

> powOp :: Parser POWOP
> powOp = symbol "^" >> return POWOP

> unaryExpr :: Parser UNARYEXPR
> unaryExpr = do
>   a <- Parsec.optionMaybe unaryOp
>   b <- term
>   return (UNARYEXPR a b)

> unaryOp :: Parser UNARYOP
> unaryOp = (symbol "-" >> return NEGOP) <|>
>   (symbol "!" >> return NOTOP)

> term :: Parser TERM
> term = (EXPR_NUMBER <$> numberLiteral) <|>
>   (TERM_FIELD <$> fieldExpr)

> fieldExpr :: Parser FIELDEXPR
> fieldExpr = do
>   a <- origin
>   b <- Parsec.optionMaybe modifiers
>   return (FIELDEXPR a b)

> origin :: Parser ORIGIN
> origin = (EXPR_TEXT <$> textLiteral) <|>
>   (EXPR_IDENTIFIER <$> identifier) <|>
>   (EXPR_FIELD <$> field) <|>
>   blockFirst <|>
>   nestedFirst
>   where
>     blockFirst = do
>       a <- blockDelimLeft
>       b <- Parsec.optionMaybe block
>       c <- blockDelimRight
>       return (EXPR_BLOCK a b c)
>     nestedFirst = do
>       a <- exprDelimLeft
>       b <- definition
>       c <- exprDelimRight
>       return (EXPR_NESTED a b c)

> modifiers :: Parser MODIFIERS
> modifiers = do
>   a <- modifier
>   b <- Parsec.optionMaybe modifiers
>   return (MODIFIERS a b)

> modifier :: Parser MODIFIER
> modifier = (OP_FIELD <$> field) <|> extendFirst where
>   extendFirst = do
>     a <- blockDelimLeft
>     b <- Parsec.optionMaybe block
>     c <- blockDelimRight
>     return (OP_EXTEND a b c)

> exprDelimLeft :: Parser EXPRDELIMLEFT
> exprDelimLeft = punctuation LEFT_PAREN $> EXPRDELIMLEFT

> exprDelimRight :: Parser EXPRDELIMRIGHT
> exprDelimRight = punctuation RIGHT_PAREN $> EXPRDELIMRIGHT

> blockDelimLeft :: Parser BLOCKDELIMLEFT
> blockDelimLeft = punctuation LEFT_BRACE $> BLOCKDELIMLEFT

> blockDelimRight :: Parser BLOCKDELIMRIGHT
> blockDelimRight = punctuation RIGHT_BRACE $> BLOCKDELIMRIGHT

> tokInfixR
>  :: (a -> Maybe (b, c) -> c)
>  -> Parser a -> Parser b -> Parser c
> tokInfixR f p op = do
>   a <- p
>   b <- Parsec.optionMaybe
>     (do
>       a <- op
>       b <- tokInfixR p op f
>       return (a, b))
>   return (f a b)

> tokInfix
>  :: (a -> Maybe (b, a) -> c)
>  -> Parser a -> Parser b -> Parser c
> tokInfix f p op = do
>   a <- p
>   b <- Parsec.optionMaybe
>     (do s <- op; b <- p; return (a, b))
>   return (f a b)

> tokInfixL
>  :: (Maybe (c, b) -> a -> c)
>  -> Parser a -> Parser b -> Parser c
> tokInfixL f p op = do a <- p; rest (f Nothing a) where
>   rest c = 
>     (do b <- op; a <- p; rest (f (Just (c, b)) a)) <|>
>     return c

For converting to syntax

> parseDefinition :: Definition_ r => DEFINITION -> r
> parseDefinition (DEFINITION a) = parseOrExpr a

> parseOrExpr :: Definition_ r => OREXPR -> r
> parseOrExpr (OREXPR a Nothing) = parseAndExpr a
> parseOrExpr (OREXPR a (Just (_, b))) =
>   parseAndExpr a #|| parseOrExpr r

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
> parseSumExpr (SUMEXPR Nothing a) = parseProductExpr a
> parseSumExpr (SUMEXPR (Just (c, b), a)) =
>   parseSumExpr c `op` parseProductExpr a
>   where
>     op = case b of ADDOP -> (+); SUBOP -> (-)

> parseProductExpr :: Definition_ r => PRODUCTEXPR -> r
> parseProductExpr (PRODUCTEXPR Nothing a) = parsePowerExpr a
> parseProductExpr (PRODUCTEXPR (Just (c, b)) a) =
>   parsePowerExpr c `op` parseProductExpr a
>   where
>     op = case b of MULOP -> (*); DIVOP -> (/)

> parsePowerExpr :: Definition_ r => POWEREXPR -> r
> parsePowerExpr (POWEREXPR a Nothing) = parseUnaryExpr a
> parsePowerExpr (POWEREXPR a (Just (_, c))) =
>   parseUnaryExpr a #^ parsePowerExpr c

> parseUnaryExpr :: Definition_ r => UNARYEXPR -> r
> parseUnaryExpr (UNARYEXPR (a, b)) = op (parseTerm b) where
>   op = case a of
>     Nothing    -> id
>     Just NEGOP -> neg
>     Just NOTOP -> not

> parseTerm :: Definition_ r => TERM -> r
> parseTerm (EXPR_NUMBER n) = parseNumberLiteral n
> parseTerm (EXPR_FIELD e) = parseFieldExpr e

> parseFieldExpr :: Definition_ r => FIELDEXPR -> r
> parseFieldExpr (FIELDEXPR a b) =
>   parseModifiers b (parseOrigin a)

> parseOrigin :: Definition_ r => ORIGIN -> r
> parseOrigin (EXPR_TEXT t) = quote_ t
> parseOrigin (EXPR_BLOCK _ b _) = parseBlock b
> parseOrigin (EXPR_IDENTIFIER i) = parseIdentifier i
> parseOrigin (EXPR_FIELD a) = parseField a
> parseOrigin (EXPR_NESTED _ b _) = parseDefinition b

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
>   showProductExpr b

> showSumOp :: SUMOP -> ShowS
> showSumOp a = showSymbolSpaced (SYMBOL s) where
>   s = case a of ADDOP -> "+"; SUBOP -> "-"

> showProductExpr :: PRODUCTEXPR -> ShowS
> showProductExpr (PRODUCTEXRP (a, b)) =
>   maybe id (\ (a, b) -> showProductExpr a . showProductOp b) a .
>     showPowerExpr b

> showProductOp :: PRODUCTOP -> ShowS
> showProductOp a = showSymbolSpaced (SYMBOL s) where
>   s = case a of MULOP -> "*"; DIVOP -> "/"

> showPowerExpr :: POWEREXPR -> ShowS
> showPowerExpr (POWEREXPR (a, b)) = showUnaryExpr a .
>   maybe id (\ (a, b) -> showPowerOp a . showPowerExpr b) b

> showPowerOp :: POWEROP -> ShowS
> showPowerOp POWEROP = showSymbolSpaced (SYMBOL "^")

> showUnaryExpr :: UNARYEXPR -> ShowS
> showUnaryExpr (UNARYEXPR (a, b)) = maybe id showUnaryOp a . 
>   showTerm b

> showUnaryOp :: UNARYOP -> ShowS
> showUnaryOp a = showSymbolSpaced (SYMBOL s) where
>   s = case a of NEGOP -> "-"; NOTOP -> "!"

> showTerm :: TERM -> ShowS
> showTerm (EXPR_FIELD e) = showFieldExpr e
> showTerm (EXPR_NUMBER n) = showNumberLiteral n

> showFieldExpr :: FIELDEXPR -> ShowS
> showFieldExpr (FIELDEXPR (a, b)) =
>   showOrigin a . showModifiers b

> showOrigin :: ORIGIN -> ShowS
> showOrigin (EXPR_TEXT t) = showTextLiteral t
> showOrigin (EXPR_BLOCK a b c) =
>   showExprDelimLeft a . maybe id showBlock b .
>   showExprDelimRight c
> showOrigin (EXPR_IDENTIFIER i) = PATH.showIdentifier i
> showOrigin (EXPR_FIELD f) = PATH.showField f
> showOrigin (EXPR_NESTED a b c) = showExprDelimLeft a .
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
>   Number NUMBERLITERAL |
>   Text TEXTLITERAL |
>   Block (Maybe BLOCK) |
>   Local IDENTIFIER |
>   Either a PATH.Self :#. IDENTIFIER |
>   a :# Maybe BLOCK |
>   a :#|| a | a :#&& a | a :#== a | a :#!= a |
>   a :#< a | a :#<= a | a :#> a | a :#>= a | a :#+ a |
>   a :#- a | a :#* a | a :#/ a | a :#^ a |
>   Neg a | Not a

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
>   f a = SUMEXPR (Nothing, toProductExpr a)
>   op a b c = SUMEXPR (Just (toSumExpr a, b), toProductExpr c)

> toProductExpr :: Free Canonical Void -> PRODUCTEXPR
> toProductExpr = f where
>   f (Free (a :#* b)) = op a MULOP b
>   f (Free (a :#/ b)) = op a DIVOP b
>   f a = PRODUCTEXPR (Nothing, toPowerExpr a)
>   op a b c = PRODUCTEXPR
>     (Just (toProductExpr a, b), toPowerExpr c)

> toPowerExpr :: Free Canonical Void -> POWEREXPR
> toPowerExpr (Free (a :#^ b)) = PRODUCTEXPR
>   (toUnaryExpr a, Just (POWOP, toPowerExpr b))
> toPowerExpr a = POWEREXPR (toUnaryExpr a, Nothing)

> toUnaryExpr :: Free Canonical Void -> UNARYEXPR
> toUnaryExpr = f where
>   f (Free (Neg a)) = op NEGOP a
>   f (Free (Not a)) = op NOTOP a
>   f a = UNARYEXPR (Nothing, toTerm a)
>   op a b = UNARYEXPR (Just a, toTerm b)

> toTerm :: Free Canonical Void -> TERM
> toTerm (Free (Number n)) = EXPR_NUMBER n
> toTerm a = EXPR_FIELD (toFieldExpr a)

> toFieldExpr :: Free Canonical Void -> FIELDEXPR
> toFieldExpr = go where
>   go (Free (Left a :#. i)) = case go a of
>     FIELDEXPR (a, b) -> FIELDEXPR (a, Just (modify b f))
>     where f = PATH.FIELD (PATH.SELECTOP, i)
>   go (Free (a :# x)) = case go a of
>     FIELDEXPR (a, b) -> FIELDEXPR (a, Just (modify b x'))
>     where x' = OP_EXTEND BLOCKDELIMLEFT x BLOCKDELIMRIGHT
>   go a = FIELDEXPR (toOrigin a, Nothing)

> modify :: Maybe MODIFIERS -> MODIFIER -> MODIFIERS
> modify Nothing c = MODIFIERS (c, Nothing)
> modify (Just (MODIFIERS (a, b))) c =
>   MODIFIERS (a, Just (modify b c))

> toOrigin :: Free Canonical Void -> ORIGIN
> toOrigin (Text t) = EXPR_TEXT t
> toOrigin (Block b) =
>   EXPR_BLOCK BLOCKDELIMLEFT b BLOCKDELIMRIGHT
> toOrigin (Local i) = EXPR_IDENTIFIER i
> toOrigin (Right PATH.Self :#. i) =
>   EXPR_FIELD (PATH.FIELD (PATH.SELECTOP, i))
> toOrigin a =
>   EXPR_NESTED EXPRDELIMLEFT (toDefinition a) EXPRDELIMRIGHT

Goat syntax interface implementation

> instance IsString DEFINITION where
>   fromString s = toDefinition (Local (fromString s))

> instance Select_ DEFINITION where
>  type Compound DEFINITION = Either DEFINITION PATH.Self
>  type Key Canonical = IDENTIFIER
>  a #. i = toDefinition (first parseDefinition a :#. i)

> instance Operator_ DEFINITION where
>   (#||) = toDefinition . wrap ... (:#||) `on` parseDefinition
>   (#&&) = toDefinition . wrap ...(:#&&) `on` parseDefinition
>   (#==) = toDefinition ...(:#==)
>   (#!=) = toDefinition ...(:#!=)
>   (#>) = toDefinition ...(:#>)
>   (#>=) = toDefinition ...(:#>=)
>   (#<) = toDefinition ...(:#<)
>   (#<=) = toDefinition ...(:#<=)
>   (#+) = toDefinition ...(:#+)
>   (#-) = toDefinition ...(:#-)
>   (#*) = toDefinition ...(:#*)
>   (#/) = toDefinition ...(:#/)
>   (#^) = toDefinition ...(:#^)
>   not_ = toDefinition . Not
>   neg_ = toDefinition . Neg

> instance Extend_ DEFINITION where
>   type Extension DEFINITION = Maybe BLOCK
>   (#) = toDefinition ... (:#)

> instance IsList DEFINITION where
>   type Item DEFINITION = STATEMENT
>   fromList b = toDefinition (Block (fromList b))
>   toList = error "IsList DEFINITION: toList"

> instance TextLiteral_ DEFINITION where
>   quote_ s = toDefinition (Text s)

> instance Num DEFINITION where
>   fromInteger i = toDefinition (Number (fromInteger i))
>   (+) = error "Num DEFINITION: (+)"
>   (*) = error "Num DEFINITION: (*)"
>   negate = error "Num DEFINITION: negate"
>   abs = error "Num DEFINITION: abs"
>   signum = error "Num DEFINITION: signum"
