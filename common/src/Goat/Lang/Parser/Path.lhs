> {-# LANGUAGE EmptyCase, TypeFamilies, GeneralizedNewtypeDeriving, FlexibleInstances #-}
> module Goat.Lang.Parser.Path where
> import Goat.Lang.Class
> import Text.Parsec.Text (Parser)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))
> import Control.Monad.Free.Church (MonadFree(..), F, iter)
> import Data.Functor (($>))

Path
----

A *PATH* is a *VAR* optionally followed by a  *SELECTOR*.
A *VAR* is an *IDENTIFIER* or a *FIELD*
A *FIELD* is an *IDENTIFIER* prefixed by a period ('.').
A *SELECTOR* is a sequence of *FIELDS*.

    PATH := VAR [SELECTOR]
    VAR := IDENTIFIER | FIELD
    FIELD := '.' IDENTIFIER
    SELECTOR := FIELD [SELECTOR]

Concrete types implementing the corresponding Goat syntax interfaces are given below. 

> newtype PATH = PATH (VAR, Maybe SELECTOR)
> data VAR = VAR_IDENTIFIER IDENTIFIER | VAR_FIELD FIELD
> newtype FIELD = FIELD (SELECTOP, IDENTIFIER)
> newtype SELECTOR = SELECTOR (FIELD, Maybe SELECTOR)
> data SELECTOP = SELECTOP

> proofPATH = test PATH where
>   test :: Path_ a => a -> ()
>   test _ = ()

> proofSELECTOR = test SELECTOR where
>   test :: Selector_ a => a -> ()
>   test _ = ()

> proofFIELD = (const () :: Field_ a => a -> ()) FIELD

Parsers for the grammar are thus

> path :: Parser PATH
> path = do
>   a <- var
>   b <- Parsec.optionMaybe selector
>   return (PATH (a, b))

> var :: Parser VAR
> var =
>   (VAR_IDENTIFIER <$> identifier) <|>
>   (VAR_FIELD <$> field)

> field :: Parser FIELD
> field = do
>   a <- selectOp
>   b <- identifier
>   return (FIELD (a, b))

> selectOp :: Parser SELECTOP
> selectOp = parseSymbol "." $> SELECTOP

> selector :: Parser SELECTOR
> selector = do
>   a <- field
>   b <- Parsec.optionMaybe selector
>   return (SELECTOR (a, b))
    
We can additionally translate these parse results to goat syntax

> parsePath :: Path_ r => PATH -> r
> parsePath (PATH (a, Nothing)) = parseVar a
> parsePath (PATH (a, Just b)) = parseSelector b (parseVar a)

> parseVar :: Var_ r => VAR -> r
> parseVar (VAR_IDENTIFIER i) = parseIdentifier
> parseVar (VAR_FIELD f) = parseField f

> parseField :: Field_ r => FIELD -> r
> parseField (FIELD (_, i)) = fromString "" #. i

> parseSelector :: Selector_ r => SELECTOR -> Compound r -> r
> parseSelector (SELECTOR (a, b)) c =
>   go (c #. parseIdentifier a) b
>   where
>     go a Nothing = a
>     go a (Just (SELECTOR (b, c))) =
>       go (a #. parseIdentifier b) c

or show the parse result as a grammatically valid string.

> showPath :: PATH -> ShowS
> showPath (PATH (a, b)) = showVar a . maybe id showSelector b

> showVar :: VAR -> ShowS
> showVar (VAR_IDENTIFIER i) = showIdentifier i
> showVar (VAR_FIELD f) = showField f

> showSelector :: SELECTOR -> ShowS
> showSelector (SELECTOR (a, b)) =
>   showField a . maybe id showSelector b

> showField :: FIELD -> ShowS
> showField (FIELD (a, b)) = showSelectOp a . showIdentifier b

> showSelectOp :: SELECTOP -> ShowS
> showSelectOp SELECTOP = showString "."

To implement the goat syntax interfaces,
we can define some helper types

> data Self = Self
> data SelfNotEmpty

> instance IsString VAR where
>   fromString s = VAR_IDENTIFIER (fromString s)

> instance IsString PATH where
>   fromString s = PATH (fromString s, Nothing)

> instance IsString a => IsString (Either a Self) where
>   fromString "" = Right Self
>   fromString s = Left (fromString s)

> instance IsString SelfNotEmpty where
>   fromString s = error ("SelfNotEmpty.fromString: "++s)

> instance Select_ FIELD where
>   type Compound FIELD = Either SelfNotEmpty Self
>   type Key FIELD = IDENTIFIER
>   Right Self #. i = FIELD (SELECTOP, i)

> instance Select_ SELECTOR where
>   type Compound SELECTOR = Either SELECTOR Self
>   type Key SELECTOR = IDENTIFIER
>   Left s #. i = selectSelector (Just s) i
>   Right Self #. i = selectSelector Nothing i

> selectSelector :: Maybe SELECTOR -> IDENTIFIER -> SELECTOR
> selectSelector Nothing i =
>   SELECTOR (FIELD (SELECTOP, i), Nothing)
> selectSelector (Just (SELECTOR (a, b))) i =
>   SELECTOR (a, Just (selectSelector b i))

> instance Select_ VAR where
>   type Compound VAR = Compound FIELD
>   type Key VAR = Key FIELD
>   a #. i = VAR_FIELD (a #. i)

> instance Select_ PATH where
>   type Compound PATH = Either PATH Self
>   type Key PATH = IDENTIFIER
>   Left (PATH (a, b)) #. i = PATH (a, Just (Left b #. i))
>   Right s #. i = PATH (Right s #. i, Nothing)

> instance Select_ a => Select_ (Either a Self) where
>   type Compound (Either a Self) = Compound a
>   type Key (Either a Self) = Key a
>   c #. i = Left (c #. i)
