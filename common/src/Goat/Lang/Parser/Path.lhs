> {-# LANGUAGE EmptyCase, TypeFamilies, GeneralizedNewtypeDeriving, FlexibleInstances, FlexibleContexts, LambdaCase #-}
> module Goat.Lang.Parser.Path where
> import Goat.Lang.Parser.Token
> import Goat.Lang.Class
> import Goat.Util ((...))
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))
> import Control.Monad.Free.Church (MonadFree(..), F, iter)
> import Data.Functor (($>))
> import Data.Function (on)
> import Data.Void (Void)

Path
----

A *PATH* is either an *IDENTIFIER*
optionally followed by a *FIELDS*,
or a *FIELD* optionally followed by *FIELDS*.
A *FIELD* is an *IDENTIFIER* prefixed by a period ('.').
*FIELDS* is a sequence of period-prefixed *IDENTIFIER*s.
A *SELECTOR* is a *FIELD* followed by *FIELDS*.

    PATH := IDENTIFIER FIELDS | FIELD FIELDS
    FIELD := '.' IDENTIFIER
    FIELDS := ['.' IDENTIFIER FIELDS]
    SELECTOR := FIELD FIELDS

Concrete types implementing the corresponding Goat syntax interfaces are given below. 

> data PATH =
>     PATH_IDENTIFIER IDENTIFIER FIELDS
>   | PATH_FIELD FIELD FIELDS
> newtype FIELD = FIELD_SELECTOP IDENTIFIER
> data FIELDS = FIELDS_START | FIELDS_SELECTOP FIELDS IDENTIFIER
> data SELECTOR = SELECTOR FIELD FIELDS

> proofPath :: PATH -> PATH
> proofPath = parsePath

> proofField :: FIELD -> FIELD
> proofField = parseField

> proofSelector :: SELECTOR -> SELECTOR
> proofSelector s = parseSelector s

Parsers for the grammar are thus

> path :: Parser PATH
> path = identifierFirst <|> fieldFirst where
>   identifierFirst = do
>     a <- identifier
>     b <- fields
>     return (PATH_IDENTIFIER a b)
>   fieldFirst = do
>     a <- field
>     b <- fields
>     return (PATH_FIELD a b)

> field :: Parser FIELD
> field = symbol "." >> (FIELD_SELECTOP <$> identifier)

> fields :: Parser FIELDS
> fields = go FIELDS_START where
>   go a = do
>     symbol "."
>     b <- identifier
>     go (FIELDS_SELECTOP a b)
>     <|> return a

> selector :: Parser SELECTOR
> selector = do
>   a <- field
>   b <- fields
>   return (SELECTOR a b)
    
We can additionally translate these parse results to goat syntax

> parsePath :: Path_ r => PATH -> r
> parsePath = \case
>   PATH_IDENTIFIER ii FIELDS_START ->
>     parseIdentifier ii
>   
>   PATH_IDENTIFIER ii (FIELDS_SELECTOP fs i) ->
>     parsePath (PATH_IDENTIFIER ii fs) #. parseIdentifier i
>   
>   PATH_FIELD ff FIELDS_START ->
>     parseField ff
>   
>   PATH_FIELD ff (FIELDS_SELECTOP fs i) ->
>     parsePath (PATH_FIELD ff fs) #. parseIdentifier i

> parseField :: Field_ r => FIELD -> r
> parseField (FIELD_SELECTOP i) =
>   fromString "" #. parseIdentifier i

> parseSelector
>  :: Selector_ r => SELECTOR -> r
> parseSelector (SELECTOR ff FIELDS_START) = parseField ff
> parseSelector (SELECTOR ff (FIELDS_SELECTOP fs i)) =
>   parseSelector (SELECTOR ff fs) #. parseIdentifier i

or show the parse result as a grammatically valid string.

> showPath :: PATH -> ShowS
> showPath (PATH_IDENTIFIER i fs) =
>   showIdentifier i . showFields fs
> showPath (PATH_FIELD f fs) = showField f . showFields fs

> showField :: FIELD -> ShowS
> showField (FIELD_SELECTOP a) =
>   showSymbol (SYMBOL ".") . showIdentifier a

> showFields :: FIELDS -> ShowS
> showFields FIELDS_START = id
> showFields (FIELDS_SELECTOP fs i) =
>   showFields fs .
>   showSymbol (SYMBOL ".") .
>   showIdentifier i

> showSelector :: SELECTOR -> ShowS
> showSelector (SELECTOR f fs) = showField f . showFields fs

To implement the goat syntax interfaces,
we adds an empty string interpretation to our types via a 'Self' helper type.

> instance IsString PATH where
>   fromString s = PATH_IDENTIFIER (fromString s) FIELDS_START

> instance Select_ FIELD where
>   type Selects FIELD = Either Self (NotString Void)
>   type Key FIELD = IDENTIFIER
>   Left Self #. i = FIELD_SELECTOP i

> instance Select_ PATH where
>   type Selects PATH = Either Self PATH
>   type Key PATH = IDENTIFIER
>   Left s #. i = PATH_FIELD (FIELD_SELECTOP i) FIELDS_START
>   Right (PATH_IDENTIFIER a fs) #. i =
>     PATH_IDENTIFIER a (FIELDS_SELECTOP fs i)
>   Right (PATH_FIELD a fs) #. i =
>     PATH_FIELD a (FIELDS_SELECTOP fs i)

> instance Select_ SELECTOR where
>   type Selects SELECTOR = Either Self (NotString SELECTOR)
>   type Key SELECTOR = IDENTIFIER
>   Left s #. i = SELECTOR (FIELD_SELECTOP i) FIELDS_START
>   Right (NotString (SELECTOR a fs)) #. i =
>     SELECTOR a (FIELDS_SELECTOP fs i)

The helper type 'Self' can be used to add an interpretation for the empty string ("") to a type implementing the Goat syntax interface.

> data Self = Self
> newtype NotString a = NotString a
> notSelf :: Either Self a -> a
> notSelf (Left Self) = error "Invalid use of Self"
> notSelf (Right a) = a

> instance IsString (NotString a) where
>   fromString s = error ("NotString.fromString: "++s)

> instance IsString a => IsString (Either Self a) where
>   fromString "" = Left Self
>   fromString s = pure (fromString s)

> instance Select_ a => Select_ (NotString a) where
>   type Selects (NotString a) = Selects a
>   type Key (NotString a) = Key a
>   c #. i = NotString (c #. i)

> instance Select_ a => Select_ (Either Self a) where
>   type Selects (Either Self a) = Selects a
>   type Key (Either Self a) = Key a
>   c #. i = pure (c #. i)

> instance Extend_ a => Extend_ (Either Self a) where
>   type Extension (Either Self a) = Extension a
>   a # x = pure (notSelf a # x)

> instance Operator_ a => Operator_ (Either Self a) where
>   (#+) = pure ... (#+) `on` notSelf
>   (#-) = pure ... (#-) `on` notSelf
>   (#*) = pure ... (#*) `on` notSelf
>   (#/) = pure ... (#/) `on` notSelf
>   (#^) = pure ... (#^) `on` notSelf
>   (#>) = pure ... (#>) `on` notSelf
>   (#>=) = pure ... (#>=) `on` notSelf
>   (#<) = pure ... (#<) `on` notSelf
>   (#<=) = pure ... (#<=) `on` notSelf
>   (#==) = pure ... (#==) `on` notSelf
>   (#!=) = pure ... (#!=) `on` notSelf
>   (#||) = pure ... (#||) `on` notSelf
>   (#&&) = pure ... (#&&) `on` notSelf
>   neg_ = pure . neg_ . notSelf
>   not_ = pure . not_ . notSelf

> instance IsList a => IsList (Either Self a) where 
>   type Item (Either Self a) = Item a
>   fromList b = pure (fromList b)
>   toList = error "IsList (Either Self a): toList"

> instance TextLiteral_ a => TextLiteral_ (Either Self a) where
>   quote_ a = pure (quote_ a)

> instance Num a => Num (Either Self a) where
>   fromInteger i = pure (fromInteger i)
>   (+) = error "Num (Either Self a): (+)"
>   (*) = error "Num (Either Self a): (*)"
>   negate = error "Num (Either Self a): negate"
>   abs = error "Num (Either Self a): abs"
>   signum = error "Num (Either Self a): signum"

> instance Fractional a => Fractional (Either Self a) where
>   fromRational r = pure (fromRational r)
>   (/) = error "Fractional (Either Self a): (/)"
