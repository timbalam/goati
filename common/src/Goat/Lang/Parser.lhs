## Goat language grammar

This module defines and implements the parser grammar of the Goat programming language.
The module also defines translations to the Goat syntax defined in module 'Goat.Lang.Class'.

> module Goat.Lang.Parser where
> import qualified Goat.Lang.Path as PATH
> import qualified Goat.Lang.Pattern as PATTERN
> import Goat.Lang.Class
> import Goat.Util ((...))
> import Goat.Comp (MonadFree(..), Comp, comp)
> import Data.Monoid (Endo(..))
> import Text.Parsec.Text (Parser)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))

### Block

A *BLOCK* is a sequence of *STATEMENT*s separated and optionally terminated by literal semi-colons (';').
A source file will often consist of a single block.

    BLOCK := STATEMENT [';' [BLOCK]]

We can represent a *BLOCK* concretely with a type synonym

> type BLOCK = [STATEMENT]

which implements the 'Block_ BLOCK' Goat syntax interface

> proofBLOCK = test BLOCK where
>   test :: Block_ a => a -> ()
>   test _ = ()

To parse (note the type generalises 'Parser BLOCK'): 

> parseBlock :: Statement_ r => Parser [r]
> parseBlock = Parsec.sepEndBy
>   (fromStatement <$> parseStatement)
>   (PATTERN.separator ";")

We can convert the parse result to syntax:

> fromBlock :: Block_ r => [Item r] -> r
> fromBlock = fromList

Or show it as a grammatically valid string:

> showBlock :: ShowS -> BLOCK -> ShowS
> showBlock wsep ss =
>   getEndo
>     (foldMap
>       (\ s -> Endo (showStatment s .
>         PATTERN.showSeparator ';' wsep))
>       ss)

### Statement

In terms of Goat's grammar a *STATEMENT* can have multiple forms.
The general form starts with a *PATTERNBLOCKS*,
or a *PATH* and optional *PATTERNBLOCKS*,
and finishs with an equals sign ('=') and a *DEFINITION*.
In the second form, it consists of a lone *PATH*,
omitting any *PATTERNBLOCKS*,
and the equals sign and *DEFINITION*.

    STATEMENT :=
        PATH [[PATTERNBLOCKS] '=' DEFINITION]
      | PATTERNBLOCKS '=' DEFINITION

We can concretely represent a *STATEMENT* using helper types,
and implement the Goat syntax interface 'Statement_' for it.

> data Statement p a =
>     LetPun PATH.PATH
>   | LetAssign PATTERN.PATTERN a
> type STATEMENT = Statement DEFINITION

> proofSTATEMENT = (const () :: Statement_ a => a -> ()) STATEMENT

We can parse (with type generalising 'Parser STATEMENT') with

> parseStatement
>  :: Definition_ a => Parser (Statement a)
> parseStatement = pathFirst <|> blockFirst where
>   pathFirst = do
>     path <- PATH.parsePath
>     (blockDefinitionNext (pure path) <|> return (LetPun path))
>   blockDefinitionNext path = do
>     pure path <**>
>       Parsec.option id PATTERN.parseLetExtension <**>
>       assignNext
>   blockFirst = PATTERN.parseLetBlock <**> assignNext
>   assignNext =
>     parseSymbol "=" >>
>     flip LetAssign <$> parseDefinition

We can convert the parse result to syntax with

> fromStatement
>  :: Statement_ r => Statement (Rhs r) -> r
> fromStatement (LetPun path) = PATH.fromPath path
> fromStatement (LetAssign lhs a) = PATTERN.fromPattern lhs #= a

or show the grammar as a string

> showStatement :: STATEMENT -> ShowS
> showStatement (LetPun path) = PATH.showPath path
> showStatement (LetAssign lhs def) =
>   PATTERN.showPattern lhs . showString " = " .
>     showDefinition def

We need the following Goat syntax interfaces implemented for our helper type.

> instance IsString (Statement a) where
>   fromString s = LetPun (fromString s)

> instance Select_ (Statement a) where
>   type Compound (Statement a) = Compound PATH.PATH
>   c #. i = LetPun (c #. i)

> instance Assign_ (Statement a) where
>   type Lhs (Statement a) = PATTERN.PATTERN
>   type Rhs (Statement a) = a
>   (#=) = LetAssign

## Definition

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
an *IDENTIFIER*, a *BLOCK* delimited by braces ('{}'),
or a *DEFINITION* delimited by parentheses ('()').
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

Concretely,
aftern defining some helper types with associativity to match the Goat syntax interface
    
> data OrExpr a = NoOr (AndExpr a) | OpOr (AndExpr a) (OrExpr a)
> data AndExpr a =
>   NoAnd (CompareExpr a) | OpAnd (CompareExpr a) (AndExpr a)
> data CompareExpr a =
>   NoCompare (SumExpr a) |
>   OpEq (SumExpr a) (SumExpr a) |
>   OpNe (SumExpr a) (SumExpr a) |
>   OpLt (SumExpr a) (SumExpr a) |
>   OpLe (SumExpr a) (SumExpr a) |
>   OpGt (SumExpr a) (SumExpr a) |
>   OpGe (SumExpr a) (SumExpr a)
> data SumExpr a =
>   NoSum (ProductExpr a) |
>   OpAdd (SumExpr a) (ProductExpr a) |
>   OpSub (SumExpr a) (ProductExpr a)
> data ProductExpr a =
>   NoProduct (PowerExpr a) |
>   OpMul (ProductExpr a) (PowerExpr a) |
>   OpDiv (ProductExpr a) (PowerExpr a)
> data PowerExpr a =
>   NoPower (UnaryExpr a) | OpPow (UnaryExpr a) (PowerExpr a)
> data UnaryExpr a =
>   NoUnary (Term a) | OpNeg (Term a) | OpNot (Term a)
> data Term a =
>   TermNumber NUMBERLITERAL | NoNumber (FieldExpr a)
> data FieldExpr a =
>    -- | origin
>     TermText TEXTLITERAL
>   | TermBlock [Statement a]
>   | TermLocal IDENTIFIER
>   | TermField SELF IDENTIFIER
>   | TermNested a
>    -- | modifier
>   | OpSelect (FieldExpr a) IDENTIFIER
>   | OpExtend (FieldExpr a) [Statement a]
> type DEFINITION = Comp OrExpr Void
> type OREXPR = OrExpr DEFINITION
> type ANDEXPR = AndExpr DEFNITION
> type COMPAREEXPR = CompareExpr DEFINITION
> type SUMEXPR = SumExpr DEFINITION
> type PRODUCTEXPR = ProductExpr DEFINITION
> type POWEREXPR = PowerExpr DEFINITION
> type UNARYEXPR = UnaryExpr DEFINTIION
> type FIELDEXPR = FieldExpr DEFINITION

> proofDEFINITION =
>   (const () :: Definition_ a => a -> ()) DEFINITION

To parse

> parseDefinition
>  :: Definition_ r => Parser (OrExpr r)
> parseDefinition = parseOrExpr where
>   parseOrExpr = parseInfixR parseAndExpr orOp NoOr
>   parseAndExpr = parseInfixR parseCompareExpr andOp NoAnd
>   parseCompareExpr =
>     parseInfix parseSumExpr comparisonOp NoCompare
>   parseSumExpr = parseInfixL parseProductExpr sumOp NoSum
>   parseProductExpr =
>     parseInfixL parsePowerExpr productOp NoProduct
>   parsePowerExpr =
>     parseInfixR parseUnaryExpr powOp NoPower
>   parseUnaryExpr =
>     (negOp <|> notOp <|> pure NoUnary) <*> parseTerm
>   parseTerm =
>     (TermNumber <$> parseNumberLiteral) <|>
>     (NoNumber <$> parseFieldExpr)
>   parseFieldExpr = parseOrigin <**> parseModifiers
>   parseOrigin =
>     (TermText <$> parseTextLiteral) <|>
>     (TermLocal <$> parseIdentifier) <|>
>     (fromSelect <$> parseField) <|>
>     (TermBlock <$> braces parseBlock) <|>
>     (TermNested . fromDefinition <$> parens parseDefinition)
>   parseModifiers = go id where
>     go f = (do g <- parseModifier; go (g . f)) <|> return f
>   parseModifier =
>     (parseSelect <&> \ f -> fromSelect . f) <|>
>     (braces parseBlock <&> \ b a -> OpExtend a b)
>
>   andOp = parseSymbol "&&" >> return OpAnd
>   orOp = parseSymbol "||" >> return OpOr
>   comparisonOp = 
>     (parseSymbol ">" >> return OpGt) <|>
>     (parseSymbol "<" >> return OpLt) <|>
>     (parseSymbol "==" >> return OpEq) <|>
>     (parseSymbol "!=" >> return OpNe) <|>
>     (parseSymbol ">=" >> return OpGe) <|>
>     (parseSymbol "<=" >> return OpLe)
>   sumOp =
>     (parseSymbol "+" >> return OpAdd) <|>
>     (parseSymbol "-" >> return OpSub)
>   productOp =
>     (parseSymbol "*" >> return OpMul) <|>
>     (parseSymbol "/" >> return OpDiv)
>   powOp = parseSymbol "^" >> return OpPow
>   negOp = parseSymbol "-" >> return OpNeg
>   notOp = parseSymbol "!" >> return OpNot
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

For converting to syntax

> fromOrExpr :: Definition_ r => OrExpr r -> r
> fromOrExpr (NoOr n) = fromAndExpr n
> fromOrExpr (OpOr n r) = fromAndExpr #|| fromOrExpr r

> fromAndExpr :: Definition_ r => AndExpr r -> r
> fromAndExpr (NoAnd m) = fromCompareExpr m
> fromAndExpr (OpAnd m n) = fromCompareExpr m #&& fromAndExpr n

> fromCompareExpr :: Definition_ r => CompareExpr r -> r
> fromCompareExpr (NoCompare a) = fromSumExpr a
> fromCompareExpr (OpEq a b) = fromSumExpr a #== fromSumExpr b
> fromCompareExpr (OpNe a b) = fromSumExpr a #!= fromSumExpr b
> fromCompareExpr (OpLt a b) = fromSumExpr a #< fromSumExpr b
> fromCompareExpr (OpLe a b) = fromSumExpr a #<= fromSumExpr b
> fromCompareExpr (OpGt a b) = fromSumExpr a #> fromSumExpr b
> fromCompareExpr (OpGe a b) = fromSumExpr a #>= fromSumExpr b

> fromSumExpr :: Definition_ r => SumExpr r -> r
> fromSumExpr (NoSum d) = fromProductExpr d
> fromSumExpr (OpAdd s d) = fromSumExpr s #+ fromProductExpr d
> fromSumExpr (OpSub s d) = fromSumExpr s #- fromProductExpr d

> fromProductExpr :: Definition_ r => PowerExpr r -> r
> fromProductExpr (NoProduct w) = fromPowerExpr w
> fromProductExpr (OpMul w d) =
>   fromPowerExpr w #* fromProductExpr d
> fromProductExpr (OpDiv w d) =
>   fromPowerExpr w #/ fromProductExpr d

> fromPowerExpr :: Definition_ r => PowerExpr r -> r
> fromPowerExpr (NoPower u) = fromUnaryExpr u
> fromPowerExpr (OpPow u w) = fromUnaryExpr u #^ fromPowerExpr w

> fromUnaryExpr :: Definition_ r => UnaryExpr r -> r
> fromUnaryExpr (NoUnary t) = fromTerm t
> fromUnaryExpr (OpNeg t) = neg_ (fromTerm t)
> fromUnaryExpr (OpNot t) = not_ (fromTerm t)

> fromTerm :: Definition_ r => Term r -> r
> fromTerm (TermNumber n) = fromNumberLiteral n
> fromTerm (NoNumber e) = fromFieldExpr e

> fromFieldExpr
>  :: Definition_ r => FieldExpr r -> r
> fromFieldExpr (TermText t) = quote_ t
> fromFieldExpr (TermBlock b) = fromBlock b
> fromFieldExpr (TermLocal i) = fromIdentifier i
> fromFieldExpr (TermField s i) = Right s #. i
> fromFieldExpr (TermNested r) = r
> fromFieldExpr (OpSelect e i) = Left (fromFieldExpr e) #. i
> fromFieldExpr (OpExtend e b) = fromFieldExpr e # b

and for showing

> showDefinition :: DEFINITION -> ShowS
> showDefinition m = comp absurd showOrExpr m 

> showOrExpr :: OREXPR -> ShowS
> showOrExpr (NoOr n) = showAndExpr n
> showOrExpr (OpOr n r) =
>  showAndExpr n . showString " || " . showOrExpr r

> showAndExpr :: ANDEXPR -> ShowS
> showAndExpr (NoAnd m) = showCompareExpr m
> showAndExpr (OpAnd m n) =
>   showCompareExpr m . showString " && " . showAndExpr n

> showCompareExpr :: COMPAREEXPR -> ShowS
> showCompareExpr = show' where
>   show' (NoCompare a) = showSumExpr a
>   show' (OpEq a b) = infix' " == " a b
>   show' (OpNe a b) = infix' " != " a b
>   show' (OpLt a b) = infix' " < " a b
>   show' (OpLe a b) = infix' " <= " a b
>   show' (OpGt a b) = infix' " > " a b
>   show' (OpGe a b) = infix' " >= " a b
>   infix' s a b = showSumExpr a . showString s . showSumExpr b

> showSumExpr :: SUMEXPR -> ShowS
> showSumExpr (NoSum d) = showProductExpr d
> showSumExpr (OpAdd s d) =
>   showSumExpr s . showString " + " . showProductExpr d
> showSumExpr (OpSub s d) =
>   showSumExpr s . showString " - " . showProductExpr d

> showProductExpr :: PRODUCTEXPR -> ShowS
> showProductExpr (NoProduct w) = showPowerExpr w
> showProductExpr (OpMul d w) =
>   showProductExpr d . showString " * " . showProductExpr w
> showProductExpr (OpDiv d w) = 
>   showProductExpr d . showString " / " . showProductExpr w

> showPowerExpr :: POWEREXPR -> ShowS
> showPowerExpr (NoPower u) = showUnaryExpr u
> showPowerExpr (OpPow u w) =
>   showUnaryExpr u . showString " ^ " . showPowerExpr w

> showUnaryExpr :: UNARYEXPR -> ShowS
> showUnaryExpr (NoUnary t) = showTerm t
> showUnaryExpr (OpNeg t) = showString "-" . showTerm t
> showUnaryExpr (OpNot t) = showString "!" . showTerm t

> showTerm :: TERM -> ShowS
> showTerm (NoNumber e) = showFieldExpr e
> showTerm (TermNumber n) = showNumberLiteral n

> showFieldExpr :: FIELDEXPR -> ShowS
> showFieldExpr (TermText t) = showTextLiteral t
> showFieldExpr (TermBlock b) = PATTERN.showBraces (showBlock b)
> showFieldExpr (TermLocal i) = PATH.showIdentifier i
> showFieldExpr (TermField s i) =
>   PATH.showSelect (PATH.showSelf s) i
> showFieldExpr (TermNested d) = showParen True (showDefinition d)
> showFieldExpr (OpSelect e i) =
>   PATH.showSelect (showFieldExpr e) i
> showFieldExpr (OpExtend e b) =
>   showFieldExpr e . PATTERN.showBraces (showBlock b)


we define a helper type for a canonical expression representation

> data Canonical a =
>   Number DecimalFloat |
>   Text String |
>   Block [Statement a] |
>   Local IDENTIFIER |
>   (Either a SELF) :#. IDENTIFIER |
>   a :# [Statement a] |
>   a :#|| a | a :#&& a | a :#== a | a :#!= a |
>   a :#< a | a :#<= a | a :#> a | a :#>= a | a :#+ a |
>   a :#- a | a :#* a | a :#/ a | a :#^ a |
>   Neg a | Not a

and conversions

> instance Field_ (F Canonical a) where
>   type Compound (F Canonical a) = Either (F Canonical a) SELF
>   (#.) = wrap ... (:#.)

> instance Definition_ a => Operator_ (F Canoncial a) where
>   (#||) = wrap ... (:#||)
>   (#&&) = wrap ... (:#&&)
>   (#==) = wrap ... (:#==)
>   (#!=) = wrap ... (:#!=)
>   (#>) = wrap ... (:#>)
>   (#>=) = wrap ... (:#>=)
>   (#<) = wrap ... (:#<)
>   (#<=) = wrap ...(:#<=)
>   (#+) = wrap ... (:#+)
>   (#-) = wrap ... (:#-)
>   (#*) = wrap ... (:#*)
>   (#/) = wrap ... (:#/)
>   (#^) = wrap ... (:#^)
>   not_ = wrap . UnaryNot
>   neg_ = wrap . UnaryNeg

> instance Extend_ (F Canoncial a) where
>   type Extension (F Canonical a) = [Statement a]
>   (#) = wrap ... (:#)

> instance IsList (Canonical a) where
>   type Item (Canonical a) = Statement a
>   fromList = wrap . Block
>   toList = error "IsList (Canonical a): toList"

> instance TextLiteral_ (Canonical a) where
>   quote_ s = Text s
