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

> instance Field_ (FieldExpr a) where
>   type Compound (FieldExpr a) = FieldExpr a
>   (#.) = (:#.)
> instance Field_ (Canonical a) where
>   type Compound (Canonical a) = FieldExpr a
>   (#.) = Term . FieldExpr ... (:#.)

> data Canonical a =
>   Term (Term a) | Or a a | And a a | Eq a a | Neq a a |
>   Lt a a | Le a a | Gt a a | Ge a a | Add a a |
>   Sub a a | Mul a a | Div a a | Pow a a |
>   UnaryNeg a | UnaryNot a
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