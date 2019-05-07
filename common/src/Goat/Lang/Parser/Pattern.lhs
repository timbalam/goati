> module Goat.Lang.Parser.Pattern where
> import qualified Goat.Lang.Parser.Path as PATH
> import Goat.Lang.Class
> import Data.Monoid (Endo(..))
> import Text.Parsec.Text (Parser)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))
> import Control.Monad.Free.Church (MonadFree(..), F, iter)

## Pattern

A *PATTERN* can start with a *PATH*,
optionally followed by a sequence of *PATTERNBLOCK*s delimited by braces
('{}').
Alternatively, it can be a sequence of brace-delimited *PATTERNBLOCK*s.

    PATTERNBLOCKS := '{' PATTERNBLOCK '}' [PATTERNBLOCKS]
    PATTERN := PATH [PATTERNBLOCKS] | PATTERNBLOCKS
    
We can represent the grammar concretely

> data Pattern a =
>     LetBlock (PatternBlock a)
>   | LetExtend a (PatternBlock a)
> type PATTERN = F Pattern PATH.PATH

such that 'Pattern_ PATTERN' is implemented.

> proofPATTERN = test PATTERN where
>   test :: Pattern_ a => a -> ()
>   test _ = ()

The grammar can be parsed with the following (note that the type generalising 'Parser PATTERN')

> parsePattern :: Pattern_ a => Parser (F Pattern a)
> parsePattern =
>   parseLetBlock <|>
>   (PATH.parsePath <&> PATH.fromPath <**> parseLetExtend)

> parseLetExtend
>  :: Parser (F Pattern a -> F Pattern a)
> parseLetExtend = do
>   b <- braces parsePatternBlock
>   (do g <- parseLetExtend; return (g . (`LetExtend` b))) <|>
>     return (`LetExtend` b)

> parseLetBlock :: Parser (F Pattern a)
> parseLetBlock =
>   braces parsePatternBlock <&> fromPatternBlock <**>
>     Parsec.option id parseLetExtension

> braces = Parsec.between
>   (Parsec.char '{' >> whitespace)
>   (Parsec.char '}' >> whitespace)

For converting grammar to syntax

> fromPattern
>  :: Pattern_ r => F Pattern r -> r
> fromPattern = iter fromPattern' where
>   fromPattern' (LetBlock b) = fromPatternBlock b
>   fromPattern' (LetExtend r b) = r # fromPatternBlock b

For showing

> showPattern :: PATTERN -> ShowS
> showPattern m = iter showPattern' (PATH.showPath <$> m) where
>   showPattern' (LetBlock b) = showBraces (showPatternBlock b)
>   showPattern' (LetExtend s b) =
>     s . showBraces (showPatternBlock b)

> showBraces s = showChar '{' . s . showChar '}'

We need the following Goat syntax interfaces implemented for our helper type.

> instance IsString a => IsString (F Pattern a) where
>   fromString s = pure (fromString s)

> instance Select_ a => Select_ (F Pattern a) where
>   type Compound (F Pattern a) = Compound a
>   c #. i = pure (c #. i)

> instance Extend_ (F Pattern a) where
>   type Extension (F Pattern a) = PatternBlock a
>   a # b = wrap (LetExtend a b)

> instance IsList (F Pattern a) where
>   type Item (F Pattern a) = Item (PatternBlock a)
>   fromList b = wrap (LetBlock b)
>   toList = error "IsList (F Pattern a): toList"

### PATTERNBLOCK

A *PATTERNBLOCK* is a sequence of *MATCHSTATEMENT*s,
separated by a literal semi-colon (';').

    PATTERNBLOCK := MATCHSTATEMENT [';' PATTERNBLOCK ]

Concretely 

> type PATTERNBLOCK = [MATCHSTATEMENT]

which implements 'PatternBlock_ PATTERNBLOCK'.

> proofPATTERNBLOCK =
>   (const () :: PatternBlock_ a => a -> ()) PATTERNBLOCK

A parser for the grammar

> parsePatternBlock :: MatchStatement_ r => Parser [r]
> parsePatternBlock = Parsec.sepEndBy
>   (fromMatchStatement <$> parseMatchStatement)
>   (separator ";")


> separator :: String -> Parser ()
> separator s = Parse.string s >> whitespace

The parse result can be interpreted as syntax via

> fromPatternBlock :: PatternBlock_ r => [Item r] -> r
> fromPatternBlock = fromList

and printed via

> showPatternBlock :: ShowS -> PATTERNBLOCK -> ShowS
> showPatternBlock wsep ss =
>   getEndo
>     (foldMap
>       (\ s -> Endo (showMatchStatement s .
>         showSeparator ';' wsep))
>     ss)

> showSeparator :: String -> ShowS -> ShowS
> showSeparator s wsep = showString s . wsep

### MATCHSTATEMENT

The grammar defines multiple forms for a *MATCHSTATEMENT*.
It can be an *IDENTIFIER* optionally followed by a *SELECTOR*,
or else a *SELECTOR*,
optionally followed by an equals sign ('=') and a *PATTERN*.

    MATCHSTATEMENT :=
        IDENTIFIER [SELECTOR]
      | SELECTOR ['=' PATTERN]

Concretely, and with demonstrated 'MatchStatement_' instance.

> data MatchStatement a =
>     MatchPun PATH
>   | MatchAssign SELECTOR a
> type MATCHSTATEMENT = MatchStatement PATTERN

> proofMATCHSTATEMENT =
>   (const () :: MatchStatement_ a => a -> ()) MATCHSTATEMENT

A parser for the grammar is

> parseMatchStatement :: Pattern_ a => Parser (MatchStatement a)
> parseMatchStatement = identifierFirst <|> fieldFirst 
>   where
>     fieldFirst = do
>       pure (fromString "") <**> PATH.parseSelector <**>
>         (assignNext <|> pure PATH.fromSelect)
>     identifierFirst =
>       PATH.parseIdentifier <**>
>         (PATH.parseSelector <&> \ f ->
>           PATH.fromSelect . f . PATH.fromIdentifier) <|>
>         return PATH.fromIdentifier)
>     assignNext =
>       parseSymbol "=" >>
>       parsePattern <&> \ b a ->
>         MatchAssign (PATH.fromSelect a) (fromPattern b)

For converting to Goat syntax

> fromMatchStatement
>  :: MatchStatement_ r => MatchStatement (Rhs r) -> r
> fromMatchStatement (MatchPun p) = PATH.fromPath p
> fromMatchStatement (MatchAssign lhs a) =
>   PATH.fromSelector lhs #= a

and for converting to a grammar string

> showMatchStatement :: MATCHSTATEMENT -> ShowS
> showMatchStatement (MatchPun p) = PATH.showPath
> showMatchStatement (MatchAssign lhs a) =
>   PATH.showSelector lhs . showString " = " . showPattern a

