> {-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
> module Goat.Lang.Parser.Pattern where
> import Goat.Lang.Parser.Token
> import qualified Goat.Lang.Parser.Path as PATH
> import Goat.Lang.Class
> import Goat.Util ((...))
> import Data.Functor (($>))
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))

Pattern
-------

A *PATTERN* can start with a *PATH*,
optionally followed by a sequence of *PATTERNBLOCK*s delimited by braces
('{}').
Alternatively, it can be a sequence of brace-delimited *PATTERNBLOCK*s.

    PATTERNBLOCKS := '{' PATTERNBLOCK '}' [PATTERNBLOCKS]
    PATTERN := PATH [PATTERNBLOCKS] | PATTERNBLOCKS
    
We can represent the grammar concretely with a datatype implementing the 'Pattern_' syntax interface.

> newtype PATTERNBLOCKS = PATTERNBLOCKS
>   (PATTERNDELIMLEFT, Maybe PATTERNBLOCK, PATTERNDELIMRIGHT,
>     Maybe PATTERNBLOCKS)
> data PATTERNDELIMLEFT = PATTERNDELIMLEFT
> data PATTERNDELIMRIGHT = PATTERNDELIMRIGHT
> data PATTERN =
>   PATTERN_PATH (PATH.PATH, Maybe PATTERNBLOCKS) |
>   PATTERN_BLOCK PATTERNBLOCKS

> proofPattern :: PATTERN -> PATTERN
> proofPattern = parsePattern

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
>   a <- patternDelimLeft
>   b <- Parsec.optionMaybe patternBlock
>   c <- patternDelimRight
>   d <- Parsec.optionMaybe patternBlocks
>   return (PATTERNBLOCKS (a, b, c, d))

> patternDelimLeft :: Parser PATTERNDELIMLEFT
> patternDelimLeft = punctuation LEFT_BRACE $> PATTERNDELIMLEFT

> patternDelimRight :: Parser PATTERNDELIMRIGHT
> patternDelimRight =
>   punctuation RIGHT_BRACE $> PATTERNDELIMRIGHT

For converting grammar to syntax

> parsePattern :: Pattern_ r => PATTERN -> r
> parsePattern (PATTERN_PATH (a, b)) =
>   parseExtendPatternBlocks b (PATH.parsePath a)
> parsePattern (PATTERN_BLOCK b) = parsePatternBlocks b

> parsePatternBlocks :: Pattern_ r => PATTERNBLOCKS -> r
> parsePatternBlocks (PATTERNBLOCKS (_, a, _, b)) =
>   parseExtendPatternBlocks b (parsePatternBlock a)

> parseExtendPatternBlocks
>  :: Pattern_ r => Maybe PATTERNBLOCKS -> r -> r
> parseExtendPatternBlocks = go where 
>   go Nothing a = a
>   go (Just (PATTERNBLOCKS (_, a, _, b))) c =
>     go b (c # parsePatternBlock a)

For showing

> showPattern :: PATTERN -> ShowS
> showPattern (PATTERN_PATH (a, b)) =
>   PATH.showPath a . maybe id showPatternBlocks b
> showPattern (PATTERN_BLOCK b) = showPatternBlocks b

> showPatternBlocks :: PATTERNBLOCKS -> ShowS
> showPatternBlocks (PATTERNBLOCKS (a, b, c, d)) =
>   showPatternDelimLeft a .
>   maybe id (showPatternBlock (showChar ' ')) b .
>   showPatternDelimRight c . maybe id showPatternBlocks d

> showPatternDelimLeft :: PATTERNDELIMLEFT -> ShowS
> showPatternDelimLeft PATTERNDELIMLEFT =
>   showPunctuation LEFT_BRACE

> showPatternDelimRight :: PATTERNDELIMRIGHT -> ShowS
> showPatternDelimRight PATTERNDELIMRIGHT =
>   showPunctuation RIGHT_BRACE

The implementation of the 'Pattern_ PATTERN' syntax interface is as follows.

> instance IsString PATTERN where
>   fromString s = PATTERN_PATH (fromString s, Nothing)

> instance Select_ PATTERN where
>   type Compound PATTERN = Either PATH.PATH PATH.Self
>   type Key PATTERN = IDENTIFIER
>   c #. i = PATTERN_PATH (c #. i, Nothing)

> instance Extend_ PATTERN where
>   type Extension PATTERN = Maybe PATTERNBLOCK
>   PATTERN_PATH (a, b) # c =
>     PATTERN_PATH (a, Just (extendPatternBlocks b c))
>   PATTERN_BLOCK a # b =
>     PATTERN_BLOCK (extendPatternBlocks (Just a) b)

> extendPatternBlocks
>   :: Maybe PATTERNBLOCKS -> Maybe PATTERNBLOCK -> PATTERNBLOCKS
> extendPatternBlocks Nothing b = PATTERNBLOCKS 
>   (PATTERNDELIMLEFT, b, PATTERNDELIMRIGHT, Nothing)
> extendPatternBlocks (Just (PATTERNBLOCKS (a, b, c, d))) e =
>   PATTERNBLOCKS (a, b, c, Just (extendPatternBlocks d e))

> instance IsList PATTERN where
>   type Item PATTERN = MATCHSTATEMENT
>   fromList b = PATTERN_BLOCK (PATTERNBLOCKS 
>     (PATTERNDELIMLEFT, fromList b, PATTERNDELIMRIGHT, Nothing))
>   toList = error "PATTERN.toList"

Pattern block
-------------

A *PATTERNBLOCK* is a sequence of *MATCHSTATEMENT*s,
separated and optionally terminated by semi-colons (';').

    PATTERNBLOCK := MATCHSTATEMENT [';' [PATTERNBLOCK]]

Our concrete datatype representation implements the 'PatternBlock_' interface.

> newtype PATTERNBLOCK = PATTERNBLOCK
>   (MATCHSTATEMENT, Maybe (PATTERNBLOCKSEP, Maybe PATTERNBLOCK))
> data PATTERNBLOCKSEP = PATTERNBLOCKSEP

> proofPatternBlock :: Maybe PATTERNBLOCK -> Maybe PATTERNBLOCK
> proofPatternBlock = parsePatternBlock

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
> patternBlockSep = punctuation SEP_SEMICOLON $> PATTERNBLOCKSEP

The parse result can be interpreted as syntax via

> parsePatternBlock :: PatternBlock_ r => Maybe PATTERNBLOCK -> r
> parsePatternBlock b = fromList (maybe [] list b) where
>   list (PATTERNBLOCK (a, b)) =
>     parseMatchStatement a : maybe [] (maybe [] list . snd) b

and printed via

> showPatternBlock :: ShowS -> PATTERNBLOCK -> ShowS
> showPatternBlock wsep (PATTERNBLOCK (a, b)) =
>   showMatchStatement a . maybe id (\ (a, b) ->
>     showPatternBlockSep a .
>     maybe id (wsep ... showPatternBlock wsep) b) b

> showPatternBlockSep :: PATTERNBLOCKSEP -> ShowS
> showPatternBlockSep PATTERNBLOCKSEP =
>   showPunctuation SEP_SEMICOLON

Implementation of Goat syntax

> instance IsList (Maybe PATTERNBLOCK) where
>   type Item (Maybe PATTERNBLOCK) = MATCHSTATEMENT
>   fromList [] = Nothing
>   fromList (s:ss) = Just (PATTERNBLOCK
>     (s, Just (PATTERNBLOCKSEP, fromList ss)))
>   toList = error "IsList (Maybe PATTERNBLOCK): toList"

Match Statement
---------------

The grammar defines multiple forms for a *MATCHSTATEMENT*.
It can be an *IDENTIFIER* optionally followed by a *SELECTOR*,
or else a *SELECTOR*,
optionally followed by an equals sign ('=') and a *PATTERN*.

    MATCHSTATEMENT :=
        IDENTIFIER [SELECTOR]
      | SELECTOR ['=' PATTERN]

Our concrete representation with demonstrated 'MatchStatement_' instance follows.

> data MATCHSTATEMENT =
>   MATCHSTATEMENT_IDENTIFIER (IDENTIFIER, Maybe PATH.SELECTOR) |
>   MATCHSTATEMENT_FIELD
>     (PATH.SELECTOR, Maybe (MATCHSTATEMENTEQ, PATTERN))
> data MATCHSTATEMENTEQ = MATCHSTATEMENTEQ

> proofMatchStatement :: MATCHSTATEMENT -> MATCHSTATEMENT
> proofMatchStatement = parseMatchStatement

A parser for the grammar is

> matchStatement :: Parser MATCHSTATEMENT
> matchStatement = identifierFirst <|> fieldFirst where
>   identifierFirst = do
>     a <- identifier
>     b <- Parsec.optionMaybe PATH.selector
>     return (MATCHSTATEMENT_IDENTIFIER (a, b))
>   fieldFirst = do
>     a <- PATH.selector
>     b <- Parsec.optionMaybe
>       (do
>         a <- matchStatementEq
>         b <- pattern
>         return (a, b))
>     return (MATCHSTATEMENT_FIELD (a, b))

> matchStatementEq :: Parser MATCHSTATEMENTEQ
> matchStatementEq = symbol "=" $> MATCHSTATEMENTEQ

For converting to Goat syntax

> parseMatchStatement :: MatchStatement_ r => MATCHSTATEMENT -> r
> parseMatchStatement (MATCHSTATEMENT_IDENTIFIER (a, Nothing)) =
>   parseIdentifier a
> parseMatchStatement (MATCHSTATEMENT_IDENTIFIER (a, Just b)) =
>   PATH.parseSelector b (parseIdentifier a)
> parseMatchStatement (MATCHSTATEMENT_FIELD (a, Nothing)) =
>   PATH.parseSelector a (fromString "")
> parseMatchStatement (MATCHSTATEMENT_FIELD (a, Just (_, b))) =
>   PATH.parseSelector a (fromString "") #= parsePattern b 

and for converting to a grammar string

> showMatchStatement :: MATCHSTATEMENT -> ShowS
> showMatchStatement (MATCHSTATEMENT_IDENTIFIER (a, b)) = 
>   showIdentifier a . maybe id PATH.showSelector b
> showMatchStatement (MATCHSTATEMENT_FIELD (a, b)) =
>   PATH.showSelector a . maybe id (\ (a, b) ->
>     showChar ' ' . showMatchStatementEq a . showChar ' ' .
>     showPattern b) b

> showMatchStatementEq :: MATCHSTATEMENTEQ -> ShowS
> showMatchStatementEq MATCHSTATEMENTEQ = showSymbol (SYMBOL "=")

Goat syntax interface

> instance IsString MATCHSTATEMENT where
>   fromString s =
>     MATCHSTATEMENT_IDENTIFIER (fromString s, Nothing)

> instance Select_ MATCHSTATEMENT where
>   type Compound MATCHSTATEMENT = (Either PATH.PATH PATH.Self)
>   type Key MATCHSTATEMENT = IDENTIFIER
>   p #. i = case p #. i of
>     PATH.PATH (PATH.VAR_IDENTIFIER a, b) ->
>       MATCHSTATEMENT_IDENTIFIER (a, b)
>     PATH.PATH (PATH.VAR_FIELD a, b) ->
>       MATCHSTATEMENT_FIELD (PATH.SELECTOR (a, b), Nothing)

> instance Assign_ MATCHSTATEMENT where
>   type Lhs MATCHSTATEMENT = PATH.SELECTOR
>   type Rhs MATCHSTATEMENT = PATTERN
>   l #= r = MATCHSTATEMENT_FIELD (l, Just (MATCHSTATEMENTEQ, r))
