> {-# LANGUAGE EmptyCase #-}
> module Goat.Lang.Parser.Path where
> import Goat.Lang.Class
> import Text.Parsec.Text (Parser)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))
> import Control.Monad.Free.Church (MonadFree(..), F, iter)

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

> data Select c = Select c IDENTIFIER
> data Path a =
>     PathLocal IDENTIFIER
>   | PathSelect (Select c)
> data SELF = SELF
> data SelfNotEmpty
> type FIELD = Select SELF
> type VAR = Path SELF
> type SELECTOR = Select (F Select SELF)
> type PATH = Path (F Path SELF)

> selfNotEmpty :: SelfNotEmpty -> a
> selfNotEmpty a = case a of {}

making note of 'Path_ PATH' and  'Selector_ SELECTOR' instances.

> proofPATH = test PATH where
>   test :: Path_ a => a -> ()
>   test _ = ()

> proofSELECTOR = test SELECTOR where
>   test :: Selector_ a => a -> ()
>   test _ = ()

> proofFIELD = (const () :: Field_ a => a -> ()) FIELD

Parsers (with generalised types) for the grammar are thus

> parsePath
>  :: (Identifier_ c, Select_ c, Compound_ c ~ c)
>  => Parser (Path c)
> parsePath = do
>   var <- parseVar
>   (pure (fromVar var) <**> parseSelector <&> PathSelect) <|>
>   return var

> parseVar :: IsString c => Parser (Path c)
> parseVar =
>   (parseIdentifier <&> PathLocal) <|>
>   (parseField <&> PathSelect)

> parseField :: IsString c => Parser (Select c)
> parseField = pure (fromString "") <**> parseSelect

> parseSelect :: Parser (c -> Select c)
> parseSelect =
>   parseSymbol "." >>
>   flip Select <$> parseIdentifier

> parseSelector
>  :: (Select_ c, Compound c ~ c) => Parser (c -> Select c)
> parseSelector = do
>   f <- parseSelect
>   (parseSelector <&> \ g -> g . fromSelect . f) <|>
>   return f

We can additionally translate the parse result to goat syntax via

> fromPath, fromVar
>  :: (Identifier_ r, Select_ r) => Path (Compound r) -> r
> fromPath (PathLocal i) = fromIdentifier i
> fromPath (PathSelect f) = fromSelect f
> fromVar = fromPath

> fromSelect :: Select_ r => Select (Compound r) -> r
> fromSelect (Select c i) = c #. fromIdentifier i

or show the parse result as a grammatically valid string

> showPath :: PATH -> ShowS
> showPath m = iter showPath' (showSelf <$> wrap m) where
>   showPath' :: Path ShowS -> ShowS
>   showPath' (Identifier i) = showIdentifier i
>   showPath' (Relative f) = showSelect f

> showSelector :: SELECTOR -> ShowS
> showSelector m = iter showSelect (showSelf <$> wrap m)

> showSelf :: SELF -> ShowS
> showSelf Self = id

> showSelect :: Select ShowS IDENTIFIER -> ShowS
> showSelect (Select s i) = s . showString "." . showIdentifier i

We require from our helper types the following goat syntax interfaces.

> instance Select_ (Select c) where
>   type Compound (Select c) = c
>   type Key (Select c) = IDENTIFIER
>   (#.) = Select

> instance IsString (Path c) where
>   fromString s = PathLocal (fromString s)

> instance Select_ (Path c) where
>   type Compound (Path c) = c
>   type Key (Path c) = IDENTIFIER
>   c #. i = PathSelect (c #. i)

> instance IsString a => IsString (Either a SELF) where
>   fromString "" = Right SELF
>   fromString s = Left (fromString s)

> instance IsString SelfNotEmpty where
>   fromString _ = error "IsString SelfNotEmpty: fromString"

> instance Select_ a => Select_ (Either a SELF) where
>   type Compound (Either a SELF) = Compound a
>   type Key (Either a SELF) = Key a
>   c #. i = Left (c #. i)

> instance IsString (F Select SELF) where
>   fromString s = either selfNotEmpty pure (fromString s)

> instance IsString (F Path SELF) where
>   fromString s = either wrap pure (fromString s)

> instance Select_ (F Select a) where
>   type Compound (F Select a) = F Select a
>   type Key (F Select a) = IDENTIFIER
>   m #. i = wrap (m #. i)

> instance Select_ (F Path a) where
>   type Compound (F Path a) = F Path a
>   type Key (F Path a) = IDENTIFIER
>   m #. i = wrap (m #. i)
    
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

with instance 'Identifier_ IDENTIFIER'.

> proofIDENTIFIER = test IDENTIFIER where
>   test :: Identifier_ a => a -> ()
>   test _ = ()

We can parse an identifier with

> parseIdent :: Parser IDENTIFIER
> parseIdent =
>  (do
>    x <- Parsec.letter
>    xs <- Parsec.many Parsec.alphaNum
>    return (IDENTIFIER (x:xs))) <?>
>  "identifier"

The parse result can be converted to a type implementing the 'Identifier_' syntax interface

> fromIdentifier :: Identifier_ r => IDENTIFIER -> r 
> fromIdentifier (IDENTIFIER s) = fromString s

and converted back to a valid string

> showIdentifier :: IDENTIFIER -> ShowS
> showIdentifier (IDENTIFIER s) = showString s

The goat syntax interface implementation is required

> instance IsString IDENTIFIER where fromString = IDENTIFIER
