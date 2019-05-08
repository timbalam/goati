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
    
We can represent the grammar concretely with a datatype implementing the 'Pattern_' syntax interface.

> newtype PATTERNBLOCKS = PATTERNBLOCKS
>   (PATTERNLEFTBRACE, PATTERNBLOCK, PATTERNRIGHTBRACE, Maybe PATTERNBLOCKS)
> data PATTERN =
>   PATTERN_PATH (PATH.PATH, Maybe PATTERNBLOCKS) |
>   PATTERN_BLOCK PATTERNBLOCKS

> proofPATTERN = test PATTERN where
>   test :: Pattern_ a => a -> ()
>   test _ = ()

The grammar can be parsed with the following

> pattern :: Parser PATTERN
> pattern = pathfirst <|> blockfirst where
>   pathfirst = do
>     a <- PATH.path
>     b <- Parsec.optionMaybe patternBlocks
>     return (PATTERN_PATH (a, b))
>   blockfirst = PATTERN_BLOCK <$> patternBlocks

> patternBlocks :: Parser PATTERNBLOCKS
> patternBlocks = do
>   a <- patternLeftBrace
>   b <- patternBlock
>   c <- patternRightBrace
>   d <- Parsec.optionMaybe patternBlocks
>   return (PATTERNBLOCKS (a, b, c, d))

> patternLeftBrace :: Parser PATTERNLEFTBRACE
> patternLeftBrace = Parsec.string "{" >> whitespace $> PATTERNLEFTBRACE

> patternRightBrace :: Parser PATTERNRIGHTBRACE
> patternRightBrace = Parsec.string "}" >> whitespace $> PATTERNRIGHTBRACE

For converting grammar to syntax

> parsePattern :: Pattern_ r => PATTERN -> r
> parsePattern (PATTERN_PATH (a, b)) =
>   parseExtendPatternBlocks b (parsePath a)
> parsePattern (PATTERN_BLOCK b) = parsePatternBlocks b

> parsePatternBlocks :: Pattern_ r => PATTERNBLOCKS -> r
> parsePatternBlocks (PATTERNBLOCKS (_, a, _, b)) =
>   parseExtendPatternBlocks b (parsePatternBlock a)

> parseExtendPatternBlocks :: Pattern r => Maybe PATTERNBLOCKS -> r -> r
> parseExtendPatternBlocks = go id where 
>   go f Nothing = f
>   go f (Just (PATTERNBLOCKS (_, a, _, b))) =
>     go (f . (# parsePatternBlock a))

For showing

> showPattern :: PATTERN -> ShowS
> showPattern (PATTERN_PATH (a, b)) = PATH.showPath a . maybe id showPatternBlocks b
> showPattern (PATTERN_BLOCK b) = showPatternBlocks b

> showPatternBlocks :: PATTERNBLOCKS -> ShowS
> showPatternBlocks (PATTERNBLOCKS (a, b, c, d)) =
>   showPatternLeftBrace a . showPatternBlock b . showPatternRightBrace .
>     maybe id showPatternBlocks d

> showPatternLeftBrace :: PATTERNLEFTBRACE -> ShowS
> showPatternLeftBrace PATTERNLEFTBRACE = showChar '{'

> showPatternRightBrace :: PATTERNRIGHTBRACE -> ShowS
> showPatternRightBrace PATTERNRIGHTBRACE = showChar '}'

The implementation of the 'Pattern_ PATTERN' syntax interface is as follows.

> instance IsString PATTERN where
>   fromString s = PATTERN_PATH (fromString s, Nothing)

> instance Select_ PATTERN where
>   type Compound PATTERN = Compound PATH
>   type Key PATTERN = Key PATH
>   c #. i = PATTERN_PATH (c #. i, Nothing)

> instance Extend_ PATTERN where
>   type Extension PATTERN = PATTERNBLOCK
>   (#) = f where 
>     f (PATTERN_PATH (a, b)) c =
>       PATTERN_PATH (a, Just (extendPatternBlocks b c))
>     f (PATTERN_BLOCK a # b) =
>       PATTERN_BLOCK (extendPatternBlocks (Just a) b)

> extendPatternBlocks
>   :: Maybe PATTERNBLOCKS -> PATTERNBLOCK -> PATTERNBLOCKS
> extendPatternBlocks Nothing b = PATTERNBLOCKS 
>   (PATTERNLEFTBRACE, b, PATTERNRIGHTBRACE, Nothing)
> extendPatternBlocks (Just (PATTERNBLOCKS (a, b, c, d))) e =
>   PATTERNBLOCKS (a, b, c, Just (extendPatternBlocks d e))

> instance IsList PATTERN where
>   type Item PATTERN = Item PATTERNBLOCK
>   fromList b = PATTERN_BLOCK (PATTERNBLOCKS 
>     (PATTERNLEFTBRACE, fromList b, PATTERNRIGHTBRACE, Nothing))
>   toList = error "PATTERN.toList"

### PATTERNBLOCK

A *PATTERNBLOCK* is a sequence of *MATCHSTATEMENT*s,
separated and optionally terminated by semi-colons (';').

    PATTERNBLOCK := MATCHSTATEMENT [';' [PATTERNBLOCK]]

Our concrete datatype representation implements the 'PatternBlock_' interface.

> newtype PATTERNBLOCK = PATTERNBLOCK
>   (MATCHSTATEMENT, Maybe (PATTERNBLOCKSEP, Maybe PATTERNBLOCK))
> data PATTERNBLOCKSEP = PATTERNBLOCKSEP

> proofPATTERNBLOCK =
>   (const () :: PatternBlock_ a => a -> ()) PATTERNBLOCK

A parser for the grammar

> patternBlock :: Parser PATTERNBLOCK
> patternBlock = do
>   a <- matchStatement
>   b <- Parsec.optionMaybe
>     (do
>        a <- patternBlockSep
>        b <- Parsec.optionMaybe patternBlock
>        return (a, b))
>   return (PATTERNBLOCK (a, b))

> patternBlockSep :: Parser PATTERNBLOCKSEP
> patternBlockSep =
>   Parsec.string ";" >> whitespace $> PATTERNBLOCKSEP

The parse result can be interpreted as syntax via

> parsePatternBlock :: PatternBlock_ r => PATTERNBLOCK -> r
> parsePatternBlock b = fromList (list b) where
>   list (PATTERNBLOCK (a, b)) =
>     parseMatchStatement a : maybe [] (maybe [] list) b

and printed via
 
> showPatternBlock :: ShowS -> PATTERNBLOCK -> ShowS
> showPatternBlock wsep (PATTERNBLOCK (a, b)) =
>   showMatchStatement a . maybe (\ (a, b) ->
>     showPatternBlockSep wsep a . maybe id showPatternBlock b)

> showPatternBlockSep :: ShowS -> PATTERNBLOCKSEP -> ShowS
> showPatternBlockSep wsep PATTERNBLOCKSEP =
>   showString ";" . wsep

Implementation of Goat syntax

> instance IsList (Maybe PATTERNBLOCK) where
>   type Item PATTERNBLOCK = MATCHSTATEMENT
>   fromList [] = Nothing
>   fromList (s:ss) = Just (PATTERNBLOCK
>     (s, Just (PATTERNBLOCKSEP, fromList ss)))
>   toList =
>     errorWithoutStackTrace "IsList (Maybe PATTERNBLOCK): toList"

### MATCHSTATEMENT

The grammar defines multiple forms for a *MATCHSTATEMENT*.
It can be an *IDENTIFIER* optionally followed by a *SELECTOR*,
or else a *SELECTOR*,
optionally followed by an equals sign ('=') and a *PATTERN*.

    MATCHSTATEMENT :=
        IDENTIFIER [SELECTOR]
      | SELECTOR ['=' PATTERN]

Our concrete representation with demonstrated 'MatchStatement_' instance follows.

> data MATCHSTATEMENT =
>   MATCHSTATEMENT_IDENTIFIER (IDENTIFIER, Maybe SELECTOR) |
>   MATCHSTATEMENT_FIELD
>     (SELECTOR, Maybe (MATCHSTATEMENTEQ, PATTERN))

> proofMATCHSTATEMENT =
>   (const () :: MatchStatement_ a => a -> ()) MATCHSTATEMENT

A parser for the grammar is

> matchStatement :: Parser MATCHSTATEMENT
> matchStatement = identifierFirst <|> fieldFirst where
>   identifierFirst = do
>     a <- identifier
>     b <- Parsec.optionMaybe selector
>     return (MATCHSTATEMENT_IDENTIFIER (a, b))
>   fieldFirst = do
>     a <- selector
>     b <- Parsec.optionMaybe
>       (do
>         a <- matchStatementEq
>         b <- pattern
>         return (a, b))
>     return (MATCHSTATEMENT_FIELD (a, b))

> matchStatementEq :: Parser MATCHSTATEMENTEQ
> matchStatementEq = symbol "=" $> MATCHSTATMENTEQ

For converting to Goat syntax

> parseMatchStatement :: MatchStatement_ r => MATCHSTATEMENT -> r
> parseMatchStatement (MATCHSTATEMENT_IDENTIFIER (a, Nothing)) =
>   parseIdentifier a
> parseMatchStatement (MATCHSTATEMENT_IDENTIFIER (a, Just b)) =
>   parseSelector b (parseIdentifier a)
> parseMatchStatement (MATCHSTATEMENT_FIELD (a, Nothing)) =
>   parseSelector a (fromString "")
> parseMatchStatement (MATCHSTATEMENT_FIELD (a, Just (_, b))) =
>   parseSelector a (fromString "") #= parsePattern b

> parseSelector :: Selector r => SELECTOR -> Compound r -> r
> parseSelector 

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


and for converting to a grammar string

> showMatchStatement :: MATCHSTATEMENT -> ShowS
> showMatchStatement (MatchPun p) = PATH.showPath
> showMatchStatement (MatchAssign lhs a) =
>   PATH.showSelector lhs . showString " = " . showPattern a

