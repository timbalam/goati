## Goat language grammar

This module defines and implements the parser grammar of the Goat programming language.
The module also defines translations to the Goat syntax defined in module 'Goat.Lang.Class'.

> module Goat.Lang.Parser where
> import Goat.Lang.Class
> import Data.These (These(..), mergeTheseWith)
> import Text.Parsec.Text (Parser)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))
> import GHC.Exts (IsList(..))
> import Control.Monad.Free (MonadFree(..), Free)

> import Data.Void (Void)

### Block

A *BLOCK* is a sequence of *STATEMENT*s separated and optionally terminated by literal semi-colons (';').
A source file will often consist of a single block.

    BLOCK := STATEMENT [';' [BLOCK]]

We can represent a *BLOCK* concretely with a type synonym

> type BLOCK = [STATEMENT]

which implements the Goat syntax interface:

> proofBLOCK = test BLOCK where
>   test :: Block_ a => a -> ()
>   test _ = ()

To parse (note the type generalises 'Parser BLOCK'): 

> parseBlock :: Statement_ r => Parser [r]
> parseBlock =
>   Parsec.sepEndBy
>       (fromStatement <$> parseStatement)
>       (Parse.string ';' >> whitespace)

We can convert the parse result to syntax:

> fromBlock :: Block_ r => [Item r] -> r
> fromBlock = fromList

Or show it as a grammatically valid string:

> showBlock :: ShowS -> BLOCK -> ShowS
> showBlock wsep ss = foldr (showSep . showStatement) id ss where
>   showSep a s = a . showString ";" . wsep . s


### Statement

In terms of the grammar a *STATEMENT* is either a *PATH*,
or one or both of a *PATH* and *PATTERN* followed by an equals sign ('=') and a *DEFINITION*.

    STATEMENT :=
        PATH [[PATTERN] '=' DEFINITION]
      | PATTERN '=' DEFINITION

We can concretely represent a *STATEMENT* using helper types

> data Statement a =
>     Pun PATH
>   | LetRec LetRecLhs a
> newtype LetRecLhs = LetRecLhs (These PATH PATTERN)
> type STATEMENT = Statement PATH DEFINITION

We can parse (with type generalising 'Parser STATEMENT') with

> parseStatement
>  :: Definition_ a => Parser (Statement a)
> parseStatement = pathFirst <|> patternFirst where
>   pathFirst = do
>     path <- parsePath
>     (patternDefinitionNext path <|> return (Pun path))
>   patternDefinitionNext path = do
>     a <- recStmtLhsNext path
>     s <- parseAssign
>     b <- parseDefinition
>     return (s a b)
>   recStatmentLhsNext path = do 
>     pattern <- Parsec.optionMaybe parsePattern
>     return (LetRecLhs (maybe (This path) (These path) pattern))
>   patternFirst = do
>     a <- LetRecLhs . That <$> parsePattern
>     s <- parseAssign
>     b <- parseDefinition
>     return (s a b)  

> parseAssign :: Assign_ r => Parser (Lhs r -> Rhs r -> r)
> parseAssign = parseSymbol "=" >> whitespace >> return (#=)

We can implement the Goat syntax interface for our helper type,
and thus for 'STATEMENT'.

> instance Field_ (Statement a) where
>   type Compound (Statement a) = Compound PATH
>   c #. i = Pun (c #. i)

> instance Assign_ (Statement a) where
>   type Lhs (Statement a) = LetRecLhs
>   type Rhs (Statement a) = a
>   (#=) = LetRec

> proofSTATEMENT = test STATEMENT where
>   test :: Statement_ a => a -> ()
>   test _ = ()

We can convert the parse result to syntax with

> fromStatement
>  :: Statement_ r => Statement (Compound r) (Rhs r) -> r
> fromStatement (Pun path) = fromPath path
> fromStatement (LetRec lhs a) = fromLetRecLhs lhs #= a

> fromLetRecLhs
>  :: (Path_ r, Pattern_ r) => LetRecLhs (Compound r) -> r
> fromLetRecLhs (LetRecLhs ths) =
>   these
>     fromPath
>     fromPattern
>     (\ a b -> fromPath a # fromPattern b)

or show the grammar as a string

> showStatement :: STATEMENT -> ShowS
> showStatement (Pun path) = showPath path
> showStatement (LetRec lhs def) =
>   showAssign (showLetRecLhs lhs) (showDefinition def)

> showLetRecLhs :: LetRecLhs -> ShowS
> showLetRecLhs (LetRecLhs ths) =
>   mergeTheseWith (.) showPath showPattern ths

> showAssign :: ShowS -> ShowS -> ShowS
> showAssign slhs srhs = slhs . showString " = " . srhs

## Path

A *PATH* is a *VAR* optionally followed by a  *SELECTOR*.
A *VAR* is an *IDENTIFIER* or a *FIELD*
A *FIELD* is an *IDENTIFIER* prefixed by a period ('.').
A *SELECTOR* is a sequence of *FIELDS*.

    PATH := VAR [SELECTOR]
    VAR := IDENTIFIER | FIELD
    FIELD := '.' IDENTIFIER
    SELECTOR := FIELD [SELECTOR]

Concretely, with helper types

> data Field c = Field c IDENTIFIER
> type Local = Either IDENTIFIER
> type Path c = Local (Field c)
> data SELF = SELF
> data SelfNotEmpty
> type Public c = Field (Either c SELF)
> type Selectors c = Field (Free Field (Either c SELF))
> type FIELD = Public SelfNotEmpty
> type VAR = Local FIELD
> type SELECTOR = Public (Selector SelfNotEmpty)
> type PATH = Local (Public (Local (Selector IDENTIFIER)))

Parsers (with generalised types) for the grammar are thus

> parsePath
>  :: (Identifier_ c, Field_ c, Compound_ c ~ c)
>  => Parser (Path c)
> parsePath = do
>   var <- parseVar
>   (parseSelector <*> pure (fromPath var) <&> Right) <|>
>   return var

> parseVar :: IsString c => Parser (Path c)
> parseVar =
>   (parseIdentifier <&> Left) <|>
>   (parseField <*> pure (fromString "") <&> Right)

> parseField :: Parser (c -> Field c)
> parseField =
>   parseSymbol "." >>
>   whitespace >>
>   (flip field <$> parseIdentifier)

> parseSelector
>  :: (Field_ c, Compound c ~ c) => Parser (c -> Field c)
> parseSelector = do
>   f <- parseField
>   (do g <- parseSelector; return (g . fromField . f)) <|>
>   return f

We can additionally translate the parse result to goat syntax via

> fromPath
>  :: (Identifier_ r, Field_ r) => Var (Compound r) -> r
> fromVar (Left i) = fromIdentifier i
> fromVar (Right f) = fromField f

> fromField :: Field_ r => Field (Compound r) -> r
> fromField (Field c i) = c #. fromIdentifier i

or show the parse result as a grammatically valid string

> showPath :: PATH -> ShowS
> showPath m =
>   iter showField (showPure' <$> wrap' m)
>   where
>     wrap' m = wrapPath' (mapPath wrapPublic' m)

>     mapPath :: (a -> b) -> Path a -> Path b
>     mapPath = fmap . fmap

>     wrapPublic'
>      :: Either (Path (Free Field (Local b))) b
>      -> Free Field (Local b)
>     wrapPublic' (Left p) = wrapPath' p
>     wrapPublic' (Right b) = pure (Right b)

>     wrapPath'
>      :: Path (Free Field (Local a)) -> Free (Field (Local a))
>     wrapPath' (Left i) = pure (Left i)
>     wrapPath' (Right f) = wrap f

>     showPure' :: Either IDENTIFIER SELF -> ShowS
>     showPure' (Left i) = showIdentifier i
>     showPure' (Right s) = showSelf s

> showSelector :: SELECTOR -> ShowS
> showSelector m = iter showField (showSelf <$> wrap' m) where
>   wrap' m = wrap (either wrap pure <$> m)

> showSelf :: SELF -> ShowS
> showSelf Self = id

> showPath :: Path ShowS -> ShowS
> showPath (Left i) = showIdentifier i
> showPath (Right f) = showField f

> showField :: Field ShowS IDENTIFIER -> ShowS
> showField (Field s i) = s . showString "." . showIdentifier i

We can implement goat syntax interface for our concrete grammar types.

> instance Field_ (Field c) where
>   type Compound (Field c) = c
>   type Key (Field c) = IDENTIFIER
>   (#.) = Field

> instance IsString (Var c) where
>   fromString s = Left (fromString s)

> instance Field_ (Var c) where
>   type Compound (Var c) = c
>   type Key (Var c) = IDENTIFIER
>   c #. i = Right (c #. i)

> instance IsString a => IsString (Either a SELF) where
>   fromString "" = Right SELF
>   fromString s = Left (fromString s)

> instance IsString SelfNotEmpty where
>   fromString _ = error "IsString SelfNotEmpty: fromString"

> instance Field_ a => Field_ (Either a SELF) where
>   type Compound (Either a SELF) = Compound a
>   type Key (Either a SELF) = Key a
>   c #. i = Left (c #. i)

> instance IsString a => IsString (Free Field a) where
>   fromString s = pure (fromString s)

> instance Field_ (Free Field (Either a SELF)) where
>   type Compound (Free Field (Either a SELF)) =
>     Either (Free Field a) SELF
>   type Key (Free Field a) = IDENTIFIER
>   e #. i = wrap (Field (getFree e) i) where
>     getFree (Left m) = m
>     getFree (Right s) = pure (Right s)

> proofPATH = test PATH where
>   test :: Path_ a => a -> ()
>   test _ = ()

> proofSELECTOR = test SELECTOR where
>   test :: Selector_ a => a -> ()
>   test _ = ()
    
## Identifier

An *IDENTIFIER* begins with a *LETTER* ('a-Z'), 
optionally followed by a sequence of *ALPHANUMERIC* characters
, either a *LETTER* or *DIGIT* ('0-9').

    IDENTIFIER := LETTER [ALPHANUMERICS]
    LETTER := 'a' | ... | 'Z'
    ALPHANUMERICS := ALPHANUMERIC [ALPHANUMERICS]
    ALPHANUMERIC := LETTER | DIGIT

Concretely

> newtype IDENTIFIER = IDENTIFIER String

We can parse an identifier with

> parseIdent :: Parser IDENTIFIER
> parseIdent =
>  (do
>    x <- Parsec.letter
>    xs <- Parsec.many Parsec.alphaNum
>    return (x:xs)) <?>
>  "identifier"

We can implement the goat syntax interface for the parse result

> instance IsString IDENTIFIER where
>   fromString = IDENTIFIER

and 



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




## Definition

See module 'Goat.Lang.Parser.Definition'.
