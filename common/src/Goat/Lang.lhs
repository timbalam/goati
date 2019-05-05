## Goat language grammar

This module defines and implements the grammar of the Goat programming language.
The code is organised using a top-down approach,
so each of the moving parts is motivated before getting into the details.
For each part of the grammar we also define a native Haskell domain specific language (DSL) form.

> module Goat.Lang where
> import Data.List.NonEmpty (NonEmpty(..))
> import Data.These (These(..), mergeTheseWith)
> import Text.Parsec.Text (Parser)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>))
> import GHC.Exts (IsList(..))
> import Control.Monad.Free (MonadFree(..), Free)

> import Data.Void (Void)

### BLOCK

A Goat *BLOCK* describes a computation for the interpreter to run,
in the form of a set of *LETSTATEMENT*s.
A source file will often consist of a single block.

> type Block stmt = [stmt]
> type BLOCK = Block LETSTATEMENT

The textual form of Goat uses a literal semi-colon (';') to separate and optionally terminate *LETSTATEMENT*s.  

    BLOCK := LETSTATEMENT [';' [BLOCK]]

> parseBlock :: LetStmt_ stmt => Parser (Block stmt)
> parseBlock =
>   Parsec.sepEndBy parseLetStmt (Parse.string ';' >> whitespace)

> showBlock :: ShowS -> BLOCK -> ShowS
> showBlock wsep ss = foldr (showSep . showLetStmt) id ss where
>   showSep a s = a . showString ";" . wsep . s

The Haskell DSL makes use of the built-in overloaded list syntax via the 'IsList' class instances.

### LETSTATEMENT

A *LETSTATEMENT* describes one or more associations between a set of disjoint *PATH*s and *DEFINITION*s.
A *LETSTATEMENT* can have a few forms.
The first, beginning with a *PATH*,
can optionally omit the following *DEFINITION*.
This 'pun' form implicitly gets the definition from an outer scope.
Alternatively, the path (optionally along with a *PATTERN*) be given a *DEFINITION*.
In the third from we omit the *PATH* and give instead a *PATTERN* and *DEFINITION*.

> data LetStmt path def =
>     LetPun path
>   | LetAssignLhs path :#= def
> type LetAssignLhs path = These path Pattern
> type LETSTMT = LetStmt PATH DEFINITION

The textual form uses an equals sign ('=') to separate *PATH* and *PATTERN* from the *DEFINITION*.

    LETSTATEMENT :=
        PATH [[PATTERN] '=' DEFINITION]
      | PATTERN '=' DEFINITION

> parseLetStmt
>  :: (Path_ path, Definition_ def) => Parser (LetStmt path def)
> parseLetStmt = pathFirst <|> patternFirst where
>   pathFirst = do
>     path <- parsePath
>     (patternDefinitionNext path <|> return (LetPun path))
>   patternDefinitionNext path = do
>     pattern <- Parsec.optionMaybe parsePattern
>     letAssign <- parseAssign
>     def <- parseDefinition
>     return (letAssign (maybe (This path) (These path) pattern) def)
>   patternFirst = do
>     pattern <- parsePattern
>     letAssign <- parseAssign
>     def <- parseDefinition
>     return (letAssign (That pattern) def)

> showLetStmt :: LETSTMT -> ShowS
> showLetStmt (LETPUN path) = showPath path
> showLetStmt (LETASSIGN lhs def) =
>   showAssign (showLetAssignLhs lhs) (showDefinition def)

> showLetAssignLhs :: LetAssignLhs PATH -> ShowS
> showLetAssignLhs = mergeTheseWith (.) showPath showPattern

The Haskell DSL introduces an overloaded assignment operator ('#=') via typeclass. 

> class Assign_ a where
>   type Lhs a
>   type Rhs a
>   (#=) :: Lhs a -> Rhs a -> a

> instance Assign_ (LetStmt path def) where
>   type Lhs (LetStmt path def) = LetAssignLhs path
>   type Rhs (LetStmt path def) = def
>   (#=) = (:#=)

> parseAssign :: Assign_ r => Parser (Lhs r -> Rhs r -> r)
> parseAssign = parseSymbol "=" >> whitespace >> return (#=)

> showAssign :: ShowS -> ShowS -> ShowS
> showAssign slhs srhs = slhs . showString " = " . srhs

### DEFINITION

A *DEFINITION* describes a Goat value or a computation to produce one,
and corresponds to the lowest precedence operator expression *OREXPR*.
*OREXPR*, *ANDEXPR* *COMPAREEXPR*, *POWEREXPR*,
*PRODUCTEXPR* and *SUMEXPR* describe expressions possibly involving infix operations
(respectively of types logical or, logical and, comparison,
exponential, multiplication/division and addition/subtraction).
*UNARYEXPR* describes expressions possibly involving prefix unary logical or numeric operations.
The grammar defines operator precedence from lowest to highest:
logical or, logical and, comparison, addition/subtraction,
multiplication/division, exponentiation, unary.
A *TERM* is a terminal expression,
either a *NUMBERLITERAL* or a *FIELDEXPR*.
A *FIELDEXPR* describes an expression possibly involving field accesses and value extensions.
An *ORIGIN* can be a *TEXTLITERAL*, a *FIELD*,  a *BLOCK*, or a nested *DEFINITION*.
Optionally following the *ORIGIN* is a *MODIFIER*,
a sequence of field accesses or extensions.

> data OrExpr a = NoOr a | a :#|| OrExpr a
> data AndExpr a = NoAnd a | a :#&& AndExpr a
> data CompareExpr a =
>   NoCompare a |
>   a :#== a | a :#!= a | a :#> a | a :#>= a |
>   a :#< a | a :#<= a
> data SumExpr a = NoSum a | SumExpr a :#+ a | SumExpr a :#- a
> data ProductExpr a =
>   NoProduct a | ProductExpr a :#* a | ProductExpr a :#/ a
> data PowerExpr a =
>   NoExponential a | a :#^ PowerExpr a
> data UnaryExpr a = NoUnary a | UnaryNeg a | UnaryNot a
> data Term a = NumberLiteral NUMBERLITERAL | FieldExpr a
> data FieldExpr a =
>    -- | origin
>     Text TEXTLITERAL
>   | Block (Block (LetStmt a))
>   | Field IDENTIFIER
>   | Nested a
>    -- | modifier
>   | FieldExpr a :#. IDENTIFIER
>   | FieldExpr a :# Block (LetStmt a)
> newtype DEFINITION = DEFINITION OREXPR
> type OREXPR = OrExpr ANDEXPR
> type ANDEXPR = AndExpr COMPAREEXPR
> type COMPAREEXPR = CompareExpr SUMEXPR
> type SUMEXPR = SumExpr PRODUCTEXPR
> type PRODUCTEXPR = ProductExpr POWEREXPR
> type POWEREXPR = PowerExpr UNARYEXPR
> type UNARYEXPR = UnaryExpr FIELDEXPR
> type FIELDEXPR = FieldExpr DEFINITION

We summarise the symbols and operator assoicativity of the textual form in the following table:

    operator | symbol |  associativity
    logical or | '||' | right
    logial and | '&&' | right
    equal | '==' | none
    not equal | '!=' | none
    less than | '<' | none
    less or equal | '<=' | none
    greater than | '>' | none
    greater or equal | '>=' | none
    addition | '+' | left
    subtraction | '-' | left
    multiplication | '*' | left
    division | '/' | left
    exponentiation | '^' | right
    unary negation | '-' | none
    unary not | '!' | none
    field access | '.' | left
    extension | '' | left

Additionally in the textual form,
*BLOCK*s are brace-delimited ('{}'),
and nested definitions are delimited using parentheses ('()').

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
      | ['.'] IDENTIFIER
      | '{' BLOCK '}'
      | '(' DEFINITION ')'
    MODIFIERS := MODIFIER [MODIFIERS]
    MODIFIER := '.' IDENTIFIER | '{' BLOCK '}'

> parseDefinition
>  :: Definition_ r => Parser (Canonical r)
> parseDefinition = toCanonical <$> parseOrExpr where
>   parseOrExpr = parseInfixR parseAndExpr orOp NoOr
>   parseAndExpr = parseInfixR parseCompareExpr andOp NoAnd
>   parseCompareExpr =
>     parseInfix parseSumExpr comparisonOp NoCompare
>   parseSumExpr = parseInfixL parseProductExpr sumOp NoSum
>   parseProductExpr =
>     parseInfixL parsePowerExpr productOp NoProduct
>   parsePowerExpr =
>     parseInfixR parseUnaryExpr powOp NoExponential
>   parseUnaryExpr =
>     (negOp <|> notOp <|> return id) <*> parseTerm
>   parseTerm = parseNumber <|> parseFieldExpr
>   parseFieldExpr = do
>     a <- parseOrigin
>     parseModifiers a
>   parseOrigin =
>     parseText <|>
>     (parseField <*> pure "") <|>
>     braces parseBlock <|>
>     (fromCanonical <$> parens parseDefinition)
>   parseModifiers a =
>     (do f <- parseModifier; parseModifiers (f a)) <|>
>     return a
>   parseModifier =
>     parseField <|> flip (#) <$> braces parseBlock
>
>   andOp = parseSymbol "&&" >> return (:#&&)
>   orOp = parseSymbol "||" >> return (:#||)
>   comparisonOp = 
>     (parseSymbol ">" >> return (:#>)) <|>
>     (parseSymbol "<" >> return (:#<)) <|>
>     (parseSymbol "==" >> return (:#==)) <|>
>     (parseSymbol "!=" >> return (:#!=)) <|>
>     (parseSymbol ">=" >> return (:#>=)) <|>
>     (parseSymbol "<=" >> return (:#<=))
>   sumOp =
>     (parseSymbol "+" >> return (:#+)) <|>
>     (parseSymbol "-" >> return (:#-))
>   productOp =
>     (parseSymbol "*" >> return (:#*)) <|>
>     (parseSymbol "/" >> return (:#/))
>   powOp = parseSymbol "^" >> return (:#^)
>   negOp = parseSymbol "-" >> return neg_
>   notOp = parseSymbol "!" >> return not_
>
>   parseInfixR p op f = do
>     a <- p
>     (do s <- op; b <- parseInfixR p op f; return (s a b)) <|>
>     return (f a)
>   parseInfix p op f = do
>     a <- p
>     (do s <- p; b <- p; return (s a b)) <|>
>     return (f a)
>   parseInfixL p op f = do a <- p; rest a where
>     rest a = 
>      (do s <- op; b <- p; rest (s a b)) <|>
>      return (f a)


The DSL uses a canonical expression form introduced via overloaded operators via typeclass.

> data Canonical a =
>   Term (Term a) | Or a a | And a a | Eq a a | Neq a a |
>   Lt a a | Le a a | Gt a a | Ge a a | Add a a |
>   Sub a a | Mul a a | Div a a | Pow a a |
>   UnaryNeg a | UnaryNot a

> class Operator_ a where
>   (#||), (#&&), (#==), (#!=), (#>), (#>=), (#<), (#<=),
>     (#+), (#-), (#*), (#/), (#^) :: r -> r -> r
>   not_, neg_ :: r -> r
> instance Definition_ a => Operator_ (Canoncial a) where
>   (#||) = (:#||) `on` fromCanonical
>   (#&&) = (:#&&) `on` fromCanonical
>   (#==) = (:#==) `on` fromCanonical
>   (#!=) = (:#!=) `on` fromCanonical
>   (#>) = (:#>) `on` fromCanonical
>   (#>=) = (:#>=) `on` fromCanonical
>   (#<) = (:#<) `on` fromCanonical
>   (#<=) = (:#<=) `on` fromCanonical
>   (#+) = (:#+) `on` fromCanonical
>   (#-) = (:#-) `on` fromCanonical
>   (#*) = (:#*) `on` fromCanonical
>   (#/) = (:#/) `on` fromCanonical
>   (#^) = (:#^) `on` fromCanonical
>   not_ = UnaryNot . fromCanonical
>   neg_ = UnaryNeg . fromCanonical

> class Field_ a where
>   type Compound a
>   (#.) = Compound a -> IDENTIFIER -> a
> instance Field_ (FieldExpr a) where
>   type Compound (FieldExpr a) = FieldExpr a
>   (#.) = (:#.)
> instance Field_ (Canonical a) where
>   type Compound (Canonical a) = FieldExpr a
>   (#.) = Term . FieldExpr ... (:#.)

> parseField :: Field_ a => Parser (Compound a -> a)
> parseField = do
>   parseSymbol "."
>   whitespace
>   i <- parseIdentifier 
>   return (#. i)

> showField :: IDENTIFIER -> ShowS
> showField i = showString "." . showIdentifier i

> class Extend_ a where
>   type Extension a
>   type Ext a
>   (#) = Ext a -> Extension a -> a
> instance Extend_ (FieldExpr a) where
>   type Extension (FieldExpr a) = Block (LetStmt a)
>   type Ext (FieldExpr a) = FieldExpr a
>   (#) = (:#)
> instance Extend_ (Canoncial a) where
>   type Extension (Canonical a) = Block (LetStmt a)
>   type Ext (Canonical a) = FieldExpr a
>   (#) = Term . FieldExpr ... (:#)

> instance IsList (FieldExpr a) where
>   type Item (FieldExpr a) = LetStmt a
>   fromList = Block
>   toList = error "IsList (FieldExpr a): toList"
> instance IsList (Canonical a) where
>   type Item (Canonical a) = LetStmt a
>   fromList = Term . FieldExpr . Block
>   toList = error "IsList (Canonical a): toList"

> (...)
>  :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
> f ... g = \ a b -> f (g a b) -- (.) . (.)

    
### NUMBERLITERAL

A *NUMBERLITERAL* describes a literal numeric value.

> type NUMBERLITERAL =
>   BinLiteral [Int] |
>   OctLiteral [Int] |
>   HexLiteral [Int] |
>   DecLiteral [Int] |
>   Decimal [Int] |
>   DecimalFloatFrac [Int] [Int] |
>   DecimalFloatExp [Int] [Int] |
>   DecimalFloatFracExpr [Int] [Int] Exponent
> data Exponent = Exponent (Maybe Sign) [Int]
> data Sign = Positive | Negative

In the textual form,
*BINDIGITS*, *OCTDIGITS*,
*HEXDIGITS* and *INTEGER* describe a literal digit
(respectively *BINDIGIT*s, *OCTDIGIT*s, *HEXDIGIT*and *DIGIT*s) 
followed by a sequence of literal digits and underscores ('_').
*BINLITERAL*, *OCTLITERAL*,
*HEXLITERAL* and *DECLITERAL* describe integer values with a prefix-determined digits
(respectively prefixes '0b', '0o', '0x' and '0d',
and *BINDIGIT*, *OCTDIGIT*, *HEXIDIGIT* and *DIGIT* digits).
A *DECIMALFLOAT* can have several forms.
It can begin with an optional plus sign ('+') followed by an *INTEGER*,
and optionally followed by a *FRACTIONAL* part and/or an *EXPONENT* part.
Alternatively it can begin with a *FRACTIONAL* part,
optionally followed by an *EXPONENT* part.
A *FRACTIONAL* begins with a period ('.') followed by an *INTEGER*.
A *POSITIVE* sign is a plus character ('+').
A *NEGATIVE* sign is a minus character ('-').
*BINLITERAL*, *OCTLITERAL*, *HEXLITERAL* 

    NUMBERLITERAL :=
      BINLITERAL |
      OCTLITERAL |
      HEXLITERAL |
      DECLITERAL |
      DECIMAL [FLOAT] |
      FLOAT
    BINLITERAL := '0b' BINDIGITS
    BINDIGITS := BINDIGIT [['_'] BINDIGITS]
    BINDIGIT := '0' | '1'
    OCTLITERAL := '0o' OCTDIGITS
    OCTDIGITS := OCTDIGIT [['_'] OCTDIGITS]
    OCTDIGIT := '0' | ... | '7'
    HEXLITERAL := '0x' HEXDIGITS
    HEXDIGITS := HEXDIGIT [['_'] HEXDIGITS]
    HEXDIGIT := '0' | ... | '9' | 'a' | ... | 'f'
    DECLITERAL := '0d' INTEGER
    INTEGER := DIGIT [['_'] INTEGER]
    DIGIT := '0' | ... | '9'
    DECIMAL := ['+'] INTEGER
    FLOAT := FRACTIONAL [EXPONENT] | EXPONENT
    FRACTIONAL := '.' INTEGER
    EXPONENT := ECHAR [SIGN] INTEGER
    ECHAR := 'e' | 'E'
    SIGN := '+' | '-'
    
    

> data DecimalFloat = DecimalFloat Integer Integer Integer


# Text literal

A *TEXTLITERAL* describes a literal fragment of text.

### PATH

A *PATH* corresponds to a sequence of labels within a hierachical set.
A *PATH* can be given a definition by a *LETSTATEMENT*,
and used within *DEFINITIONS* to link them.
An *IDENTIFIER* can be used as a label within a *PATH*.

We define a *PATH* as an optional *IDENTIFIER* followed by a *SELECTOR*,
a sequence of *IDENTIFIER*s each with a preceeding period ('.').

    PATH := [IDENTIFIER] SELECTOR
    SELECTOR := '.' IDENTIFIER [SELECTOR]

We define an *IDENTIFIER* to begin with an alphabetic character ('a-Z'), 
optionally followed by a sequence of alphanumeric characters ('a-Z0-9').

    IDENTIFIER := ALPHACHAR [ALPHANUMSEQ]
    ALPHACHAR := 'a' | ... | 'Z'
    ALPHANUMSEQ := ALPHANUMERIC [ALPHANUMSEQ]
    ALPHANUMERIC := ALPHACHAR | '0' | ... | '9'

### PATTERN

A *PATTERN* describes the successive application of *DECOMPOSEBLOCK*s to unmatched parts of a *DEFINITION*.
A *DECOMPOSEBLOCK* describes a set of components from a value to be matched with corresponding nested *BINDING*s.

We define a *PATTERN* as a sequence of *DECOMPOSEBLOCK*s,
each surrounded by curly braces ('{}').

    PATTERN := '{' DECOMPOSEBLOCK '}' [PATTERN]

We define a *DECOMPOSEBLOCK* as a sequence of *MATCHSTATEMENT*s,
separated by a literal semi-colon (';').

    DECOMPOSEBLOCK := MATCHSTATEMENT [';' DECOMPOSEBLOCK ]

### MATCHSTATEMENT

A *MATCHSTATEMENT* describes an association between a *SELECTOR*,
and a nested *BINDING*

We define a few forms for a *MATCHSTATEMENT*.
It can be an *IDENTIFIER* optionally followed by a *SELECTOR*,
or else a *SELECTOR*,
optionally followed by an equals sign and a *BINDING*.
We define a *BINDING* as a *PATH*, a *PATTERN*, or both.

    MATCHSTATEMENT :=
        IDENTIFIER [SELECTOR] | SELECTOR ['=' BINDING]
    BINDING := PATH [PATTERN] | PATTERN

