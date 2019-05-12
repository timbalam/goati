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

> data PATTERNBLOCKS a =
>   PATTERN_BLOCKSSTART |
>   PATTERN_BLOCKSEXTENDDELIMOP (PATTERNBLOCKS a) (PATTERNBLOCK a)
> data PATTERN =
>   PATTERN_PATH PATH.PATH (PATTERNBLOCKS PATTERN) |
>   PATTERN_BLOCKDELIM
>     (PATTERNBLOCK PATTERN) (PATTERNBLOCKS PATTERN)

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

> patternBlocks :: Parser (PATTERNBLOCKS PATTERN)
> patternBlocks = go PATTERN_BLOCKSSTART where
>   go a = (do
>     punctuation LEFT_BRACE
>     b <- patternBlock
>     punctuation RIGHT_BRACE
>     go (PATTERN_BLOCKSEXTENDDELIMOP a b))
>     <|> return a

For converting grammar to syntax

> parsePattern :: Pattern_ r => PATTERN -> r
> parsePattern (PATTERN_PATH a b) = parsePatternPath a b
>   where
>     parsePatternPath
>      :: Pattern_ r => PATH.PATH -> PATTERNBLOCKS PATTERN -> r
>     parsePatternPath a PATTERN_BLOCKSSTART = PATH.parsePath a
>     parsePatternPath a (PATTERN_BLOCKSEXTENDDELIMOP bs b) =
>       parsePatternPath a bs # parsePatternBlock b
> parsePattern (PATTERN_BLOCKDELIM a b) = parsePatternBlock' a b
>   where
>     parsePatternBlock'
>      :: Pattern_ r
>      => PATTERNBLOCK PATTERN -> PATTERNBLOCKS PATTERN -> r
>     parsePatternBlock' bb PATTERN_BLOCKSSTART =
>       parsePatternBlock bb
>     parsePatternBlock' bb (PATTERN_BLOCKSEXTENDDELIMOP bs b) =
>       parsePatternBlock' bb bs # parsePatternBlock b

For showing

> showPattern :: PATTERN -> ShowS
> showPattern (PATTERN_PATH a b) =
>   PATH.showPath a . showPatternBlocks b
> showPattern (PATTERN_BLOCKDELIM a b) =
>   showPunctuation LEFT_BRACE .
>   showPatternBlock (showChar ' ') a . 
>   showPunctuation RIGHT_BRACE .
>   showPatternBlocks b

> showPatternBlocks :: PATTERNBLOCKS PATTERN -> ShowS
> showPatternBlocks PATTERN_BLOCKSSTART = id
> showPatternBlocks (PATTERN_BLOCKSEXTENDDELIMOP a b) =
>   showPatternBlocks a . 
>   showPunctuation LEFT_BRACE .
>   showPatternBlock (showChar ' ') b .
>   showPunctuation RIGHT_BRACE

The implementation of the 'Pattern_ PATTERN' syntax interface is as follows.

> instance IsString PATTERN where
>   fromString s = PATTERN_PATH (fromString s) PATTERN_BLOCKSSTART

> instance Select_ PATTERN where
>   type Selects PATTERN = Either PATH.Self PATH.PATH
>   type Key PATTERN = IDENTIFIER
>   c #. i = PATTERN_PATH (c #. i) PATTERN_BLOCKSSTART

> instance Extend_ PATTERN where
>   type Extends PATTERN = PATTERN
>   type Extension PATTERN = PATTERNBLOCK PATTERN
>   PATTERN_PATH a b # x =
>     PATTERN_PATH a (PATTERN_BLOCKSEXTENDDELIMOP b x)
>   PATTERN_BLOCKDELIM a b # x =
>     PATTERN_BLOCKDELIM a (PATTERN_BLOCKSEXTENDDELIMOP b x)

> instance IsList PATTERN where
>   type Item PATTERN = MATCHSTMT PATTERN
>   fromList b =
>     PATTERN_BLOCKDELIM (fromList b) PATTERN_BLOCKSSTART
>   toList = error "PATTERN.toList"

Pattern block
-------------

A *PATTERNBLOCK* is a sequence of *MATCHSTMT*s,
separated and optionally terminated by semi-colons (';').

    PATTERNBLOCK := [MATCHSTMT [';' PATTERNBLOCK]]

Our concrete datatype representation implements the 'PatternBlock_' interface.

> data PATTERNBLOCK a =
>   PATTERNBLOCK_END |
>   PATTERNBLOCK_STMT (MATCHSTMT a) (PATTERNBLOCK_STMT a)
> data PATTERNBLOCK_STMT a =
>   PATTERNBLOCK_STMTEND |
>   PATTERNBLOCK_STMTSEP (PATTERNBLOCK a)

> proofPatternBlock
>  :: PATTERNBLOCK PATTERN -> PATTERNBLOCK PATTERN
> proofPatternBlock = parsePatternBlock

A parser for the grammar

> patternBlock :: Parser (PATTERNBLOCK PATTERN)
> patternBlock = (do
>   a <- matchStmt
>   b <- patternBlockStmt 
>   return (PATTERNBLOCK_STMT a b))
>   <|> return PATTERNBLOCK_END

> patternBlockStmt :: Parser (PATTERNBLOCK_STMT PATTERN)
> patternBlockStmt =
>   patternBlockStmtSep <|> return PATTERNBLOCK_STMTEND
>   where
>     patternBlockStmtSep =
>       punctuation SEP_SEMICOLON >>
>       (PATTERNBLOCK_STMTSEP <$> patternBlock)

The parse result can be interpreted as syntax via

> parsePatternBlock
>  :: (PatternBlock_ r, Pattern_ (Rhs (Item r)))
>  => PATTERNBLOCK PATTERN -> r
> parsePatternBlock b = fromList (toList b) where
>   toList PATTERNBLOCK_END = []
>   toList (PATTERNBLOCK_STMT a b) = case b of 
>     PATTERNBLOCK_STMTEND -> [parseMatchStmt a]
>     PATTERNBLOCK_STMTSEP b -> parseMatchStmt a : toList b

and printed via

> showPatternBlock :: ShowS -> PATTERNBLOCK PATTERN -> ShowS
> showPatternBlock wsep PATTERNBLOCK_END = wsep
> showPatternBlock wsep (PATTERNBLOCK_STMT a b) =
>   wsep .
>   showMatchStmt a .
>   showPatternBlockStmt wsep b

> showPatternBlockStmt
>  :: ShowS -> PATTERNBLOCK_STMT PATTERN -> ShowS
> showPatternBlockStmt _wsep PATTERNBLOCK_STMTEND = id
> showPatternBlockStmt wsep (PATTERNBLOCK_STMTSEP b) =
>   showPunctuation SEP_SEMICOLON .
>   showPatternBlock wsep b

Implementation of Goat syntax

> instance IsList (PATTERNBLOCK a) where
>   type Item (PATTERNBLOCK a) = (MATCHSTMT a)
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

> data MATCHSTMT a =
>   MATCHSTMT_IDENTIFIER IDENTIFIER PATH.FIELDS |
>   MATCHSTMT_FIELD PATH.SELECTOR (MATCHSTMT_FIELD a)
> data MATCHSTMT_FIELD a =
>   MATCHSTMT_FIELDEND |
>   MATCHSTMT_FIELDEQ a

> proofMatchStmt :: MATCHSTMT PATTERN -> MATCHSTMT PATTERN
> proofMatchStmt = parseMatchStmt

A parser for the grammar is

> matchStmt :: Parser (MATCHSTMT PATTERN)
> matchStmt = identifierFirst <|> fieldFirst where
>   identifierFirst = do
>     a <- identifier
>     b <- PATH.fields
>     return (MATCHSTMT_IDENTIFIER a b)
>   fieldFirst = do
>     a <- PATH.selector
>     b <- matchStmtField
>     return (MATCHSTMT_FIELD a b)

> matchStmtField :: Parser (MATCHSTMT_FIELD PATTERN)
> matchStmtField =
>   matchStmtEq <|> return MATCHSTMT_FIELDEND
>   where
>     matchStmtEq =
>       symbol "=" >> (MATCHSTMT_FIELDEQ <$> pattern)

For converting to Goat syntax

> parseMatchStmt
>  :: (MatchStmt_ r, Pattern_ (Rhs r))
>  => MATCHSTMT PATTERN -> r
> parseMatchStmt (MATCHSTMT_IDENTIFIER a b) =
>   parseMatchStmtIdentifier a b
>   where 
>     parseMatchStmtIdentifier
>      :: Path_ r => IDENTIFIER -> PATH.FIELDS -> r
>     parseMatchStmtIdentifier a PATH.FIELDS_START =
>       parseIdentifier a
>     parseMatchStmtIdentifier a (PATH.FIELDS_SELECTOP fs i) =
>       parseMatchStmtIdentifier a fs #. parseIdentifier i
> parseMatchStmt (MATCHSTMT_FIELD a MATCHSTMT_FIELDEND) =
>   PATH.parseSelector a
> parseMatchStmt (MATCHSTMT_FIELD a (MATCHSTMT_FIELDEQ c)) =
>   PATH.parseSelector a #= parsePattern c

and for converting to a grammar string

> showMatchStmt :: MATCHSTMT PATTERN -> ShowS
> showMatchStmt (MATCHSTMT_IDENTIFIER a b) =
>   showIdentifier a .
>   PATH.showFields b
> showMatchStmt (MATCHSTMT_FIELD a b) =
>   PATH.showSelector a .
>   showMatchStmtField b

> showMatchStmtField :: MATCHSTMT_FIELD PATTERN -> ShowS
> showMatchStmtField MATCHSTMT_FIELDEND = id
> showMatchStmtField (MATCHSTMT_FIELDEQ a) =
>   showSymbolSpaced (SYMBOL "=") .
>   showPattern a

Goat syntax interface

> instance IsString (MATCHSTMT a) where
>   fromString s =
>     MATCHSTMT_IDENTIFIER (fromString s) PATH.FIELDS_START

> instance Select_ (MATCHSTMT a) where
>   type Selects (MATCHSTMT a) = Either PATH.Self PATH.PATH
>   type Key (MATCHSTMT a) = IDENTIFIER
>   p #. i = case p #. i of
>     PATH.PATH_IDENTIFIER a fs ->
>       MATCHSTMT_IDENTIFIER a fs
>
>     PATH.PATH_FIELD f fs ->
>       MATCHSTMT_FIELD (PATH.SELECTOR f fs) MATCHSTMT_FIELDEND

> instance Assign_ (MATCHSTMT a) where
>   type Lhs (MATCHSTMT a) = PATH.SELECTOR
>   type Rhs (MATCHSTMT a) = a
>   l #= r = MATCHSTMT_FIELD l (MATCHSTMT_FIELDEQ r)
