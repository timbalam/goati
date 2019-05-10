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
optionally followed by *PATTERNBLOCKS*.
Alternatively, it can be a *PATTERNBLOCK* delimited by braces
('{'), ('}'), optionally followed by *PATTERNBLOCKS*.
*PATTERNBLOCKS* is a sequence of brace-delimited *PATTERNBLOCK*s.


    PATTERNBLOCKS := ['{' PATTERNBLOCK '}' PATTERNBLOCKS]
    PATTERN :=
      PATH PATTERNBLOCKS |
      '{' PATTERNBLOCK '}' PATTERNBLOCKS 
    
We can represent the grammar concretely with a datatype implementing the 'Pattern_' syntax interface.

> data PATTERNBLOCKS =
>   PATTERN_BLOCKSSTART |
>   PATTERN_BLOCKSEXTENDDELIM PATTERNBLOCKS PATTERNBLOCK
> data PATTERN =
>   PATTERN_PATH PATH.PATH PATTERNBLOCKS |
>   PATTERN_BLOCKDELIM PATTERNBLOCK PATTERNBLOCKS

> proofPattern :: PATTERN -> PATTERN
> proofPattern = parsePattern

The grammar can be parsed with the following

> pattern :: Parser PATTERN
> pattern = pathfirst <|> blockfirst where
>   pathfirst = do
>     a <- PATH.path
>     b <- patternBlocks
>     return (PATTERN_PATH a b)
>   blockfirst = do
>     punctuation LEFT_BRACE
>     a <- patternBlock
>     punctuation RIGHT_BRACE
>     b <- patternBlocks
>     return (PATTERN_BLOCKDELIM a b)

> patternBlocks :: Parser PATTERNBLOCKS
> patternBlocks = go PATTERN_BLOCKSSTART where
>   go a = (do
>     punctuation LEFT_BRACE
>     b <- patternBlock
>     punctuation RIGHT_BRACE
>     go (PATTERN_BLOCKSEXTENDDELIM a b))
>     <|> return a

For converting grammar to syntax

> parsePattern :: Pattern_ r => PATTERN -> r
> parsePattern (PATTERN_PATH a b) =
>   parsePatternBlocks b (PATH.parsePath a)
> parsePattern (PATTERN_BLOCKDELIM a b) =
>   parsePatternBlocks b (parsePatternBlock a)

> parsePatternBlocks :: Pattern_ r => PATTERNBLOCKS -> r -> r
> parsePatternBlocks PATTERN_BLOCKSSTART b = b
> parsePatternBlocks (PATTERN_BLOCKSEXTENDDELIM a x) b =
>   parsePatternBlocks a b # parsePatternBlock x

For showing

> showPattern :: PATTERN -> ShowS
> showPattern (PATTERN_PATH a b) =
>   PATH.showPath a . showPatternBlocks b
> showPattern (PATTERN_BLOCKDELIM a b) =
>   showPunctuation LEFT_BRACE .
>   showPatternBlock (showChar ' ') a . 
>   showPunctuation RIGHT_BRACE .
>   showPatternBlocks b

> showPatternBlocks :: PATTERNBLOCKS -> ShowS
> showPatternBlocks PATTERN_BLOCKSSTART = id
> showPatternBlocks (PATTERN_BLOCKSEXTENDDELIM a b) =
>   showPatternBlocks a . 
>   showPunctuation LEFT_BRACE .
>   showPatternBlock (showChar ' ') b .
>   showPunctuation RIGHT_BRACE

The implementation of the 'Pattern_ PATTERN' syntax interface is as follows.

> instance IsString PATTERN where
>   fromString s = PATTERN_PATH (fromString s) PATTERN_BLOCKSSTART

> instance Select_ PATTERN where
>   type Compound PATTERN = Either PATH.Self PATH.PATH
>   type Key PATTERN = IDENTIFIER
>   c #. i = PATTERN_PATH (c #. i) PATTERN_BLOCKSSTART

> instance Extend_ PATTERN where
>   type Extension PATTERN = PATTERNBLOCK
>   PATTERN_PATH a b # x =
>     PATTERN_PATH a (PATTERN_BLOCKSEXTENDDELIM b x)
>   PATTERN_BLOCKDELIM a b # x =
>     PATTERN_BLOCKDELIM a (PATTERN_BLOCKSEXTENDDELIM b x)

> instance IsList PATTERN where
>   type Item PATTERN = MATCHSTMT
>   fromList b =
>     PATTERN_BLOCKDELIM (fromList b) PATTERN_BLOCKSSTART
>   toList = error "PATTERN.toList"

Pattern block
-------------

A *PATTERNBLOCK* is a sequence of *MATCHSTMT*s,
separated and optionally terminated by semi-colons (';').

    PATTERNBLOCK := [MATCHSTMT [';' PATTERNBLOCK]]

Our concrete datatype representation implements the 'PatternBlock_' interface.

> data PATTERNBLOCK =
>   PATTERNBLOCK_END |
>   PATTERNBLOCK_STMT MATCHSTMT PATTERNBLOCK_STMT
> data PATTERNBLOCK_STMT =
>   PATTERNBLOCK_STMTEND |
>   PATTERNBLOCK_STMTSEP PATTERNBLOCK

> proofPatternBlock :: PATTERNBLOCK -> PATTERNBLOCK
> proofPatternBlock = parsePatternBlock

A parser for the grammar

> patternBlock :: Parser PATTERNBLOCK
> patternBlock = (do
>   a <- matchStmt
>   b <- patternBlockStmt 
>   return (PATTERNBLOCK_STMT a b))
>   <|> return PATTERNBLOCK_END

> patternBlockStmt :: Parser PATTERNBLOCK_STMT
> patternBlockStmt =
>   patternBlockStmtSep <|> return PATTERNBLOCK_STMTEND
>   where
>     patternBlockStmtSep =
>       punctuation SEP_SEMICOLON >>
>       (PATTERNBLOCK_STMTSEP <$> patternBlock)

The parse result can be interpreted as syntax via

> parsePatternBlock :: PatternBlock_ r => PATTERNBLOCK -> r
> parsePatternBlock b = fromList (toList b) where
>   toList PATTERNBLOCK_END = []
>   toList (PATTERNBLOCK_STMT a b) = case b of 
>     PATTERNBLOCK_STMTEND -> [parseMatchStmt a]
>     PATTERNBLOCK_STMTSEP b -> parseMatchStmt a : toList b

and printed via

> showPatternBlock :: ShowS -> PATTERNBLOCK -> ShowS
> showPatternBlock wsep PATTERNBLOCK_END = wsep
> showPatternBlock wsep (PATTERNBLOCK_STMT a b) =
>   wsep .
>   showMatchStmt a .
>   showPatternBlockStmt wsep b

> showPatternBlockStmt
>  :: ShowS -> PATTERNBLOCK_STMT -> ShowS
> showPatternBlockStmt _wsep PATTERNBLOCK_STMTEND = id
> showPatternBlockStmt wsep (PATTERNBLOCK_STMTSEP b) =
>   showPunctuation SEP_SEMICOLON .
>   showPatternBlock wsep b

Implementation of Goat syntax

> instance IsList PATTERNBLOCK where
>   type Item PATTERNBLOCK = MATCHSTMT
>   fromList [] = PATTERNBLOCK_END
>   fromList (s:ss) =
>     PATTERNBLOCK_STMT
>       s
>       (PATTERNBLOCK_STMTSEP (fromList ss))
>   toList = error "IsList (Maybe PATTERNBLOCK): toList"

Match Statement
---------------

The grammar defines multiple forms for a *MATCHSTMT*.
It can be an *IDENTIFIER* followed by *FIELDS*,
or else a *SELECTOR*,
optionally followed by an equals sign ('=') and a *PATTERN*.

    MATCHSTMT :=
        IDENTIFIER FIELDS
      | SELECTOR ['=' PATTERN]

Our concrete representation with demonstrated 'MatchStmt_' instance follows.

> data MATCHSTMT =
>   MATCHSTMT_IDENTIFIER IDENTIFIER PATH.FIELDS |
>   MATCHSTMT_FIELD PATH.SELECTOR MATCHSTMT_FIELD
> data MATCHSTMT_FIELD =
>   MATCHSTMT_FIELDEND |
>   MATCHSTMT_FIELDEQ PATTERN

> proofMatchStmt :: MATCHSTMT -> MATCHSTMT
> proofMatchStmt = parseMatchStmt

A parser for the grammar is

> matchStmt :: Parser MATCHSTMT
> matchStmt = identifierFirst <|> fieldFirst where
>   identifierFirst = do
>     a <- identifier
>     b <- PATH.fields
>     return (MATCHSTMT_IDENTIFIER a b)
>   fieldFirst = do
>     a <- PATH.selector
>     b <- matchStmtField
>     return (MATCHSTMT_FIELD a b)

> matchStmtField :: Parser MATCHSTMT_FIELD
> matchStmtField =
>   matchStmtEq <|> return MATCHSTMT_FIELDEND
>   where
>     matchStmtEq =
>       symbol "=" >> (MATCHSTMT_FIELDEQ <$> pattern)

For converting to Goat syntax

> parseMatchStmt :: MatchStmt_ r => MATCHSTMT -> r
> parseMatchStmt (MATCHSTMT_IDENTIFIER a b) =
>   case b of
>     PATH.FIELDS_START ->
>       parseIdentifier a
>
>     PATH.FIELDS_SELECT fs f ->
>       PATH.selectField
>         f
>         (PATH.parseFields fs (parseIdentifier a))
> parseMatchStmt (MATCHSTMT_FIELD a b) =
>   case b of
>     MATCHSTMT_FIELDEND ->
>       PATH.parseSelector a (fromString "")
>
>     MATCHSTMT_FIELDEQ c ->
>       PATH.parseSelector a (fromString "") #= parsePattern c

and for converting to a grammar string

> showMatchStmt :: MATCHSTMT -> ShowS
> showMatchStmt (MATCHSTMT_IDENTIFIER a b) =
>   showIdentifier a .
>   PATH.showFields b
> showMatchStmt (MATCHSTMT_FIELD a b) =
>   PATH.showSelector a .
>   showMatchStmtField b

> showMatchStmtField :: MATCHSTMT_FIELD -> ShowS
> showMatchStmtField MATCHSTMT_FIELDEND = id
> showMatchStmtField (MATCHSTMT_FIELDEQ a) =
>   showSymbolSpaced (SYMBOL "=") .
>   showPattern a

Goat syntax interface

> instance IsString MATCHSTMT where
>   fromString s =
>     MATCHSTMT_IDENTIFIER (fromString s) PATH.FIELDS_START

> instance Select_ MATCHSTMT where
>   type Compound MATCHSTMT = Either PATH.Self PATH.PATH
>   type Key MATCHSTMT = IDENTIFIER
>   p #. i = case p #. i of
>     PATH.PATH_IDENTIFIER a fs ->
>       MATCHSTMT_IDENTIFIER a fs
>
>     PATH.PATH_FIELD f fs ->
>       MATCHSTMT_FIELD (PATH.SELECTOR f fs) MATCHSTMT_FIELDEND

> instance Assign_ MATCHSTMT where
>   type Lhs MATCHSTMT = PATH.SELECTOR
>   type Rhs MATCHSTMT = PATTERN
>   l #= r = MATCHSTMT_FIELD l (MATCHSTMT_FIELDEQ r)
