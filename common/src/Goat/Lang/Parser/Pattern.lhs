> {-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
> module Goat.Lang.Parser.Pattern where
> import Goat.Lang.Parser.Token
> import Goat.Lang.Parser.Path
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
>   PATTERN_PATH PATH (PATTERNBLOCKS PATTERN) |
>   PATTERN_BLOCKDELIM
>     (PATTERNBLOCK PATTERN) (PATTERNBLOCKS PATTERN)

> proofPattern :: PATTERN -> PATTERN
> proofPattern = parsePattern

The grammar can be parsed with the following

> pattern :: Parser PATTERN
> pattern = pathfirst <|> blockfirst where
>   pathfirst = do
>     a <- path
>     b <- patternBlocks pattern
>     return (PATTERN_PATH a b)
>   blockfirst = do
>     punctuation LEFT_BRACE
>     a <- patternBlock pattern
>     punctuation RIGHT_BRACE
>     b <- patternBlocks pattern
>     return (PATTERN_BLOCKDELIM a b)

> patternBlocks :: Parser p -> Parser (PATTERNBLOCKS p)
> patternBlocks p = go PATTERN_BLOCKSSTART where
>   go a = (do
>     punctuation LEFT_BRACE
>     b <- patternBlock p
>     punctuation RIGHT_BRACE
>     go (PATTERN_BLOCKSEXTENDDELIMOP a b))
>     <|> return a

For converting grammar to syntax

> parsePattern :: Pattern_ r => PATTERN -> r
> parsePattern (PATTERN_PATH a b) =
>   parsePatternPath parsePattern a b
>   where
>     parsePatternPath
>      :: Pattern_ r
>      => (a -> r) -> PATH -> PATTERNBLOCKS a -> r
>     parsePatternPath _k a PATTERN_BLOCKSSTART = parsePath a
>     parsePatternPath k a (PATTERN_BLOCKSEXTENDDELIMOP bs b) =
>       parsePatternPath k a bs # parsePatternBlock k b
> parsePattern (PATTERN_BLOCKDELIM a b) =
>   parsePatternBlock' parsePattern a b
>   where
>     parsePatternBlock'
>      :: Pattern_ r
>      => (a -> r) -> PATTERNBLOCK a -> PATTERNBLOCKS a -> r
>     parsePatternBlock' k bb PATTERN_BLOCKSSTART =
>       parsePatternBlock k bb
>     parsePatternBlock' k bb (PATTERN_BLOCKSEXTENDDELIMOP bs b) =
>       parsePatternBlock' k bb bs # parsePatternBlock k b

For showing

> showPattern :: PATTERN -> ShowS
> showPattern (PATTERN_PATH a b) =
>   showPath a . showPatternBlocks showPattern b
> showPattern (PATTERN_BLOCKDELIM a b) =
>   showPunctuation LEFT_BRACE .
>   showPatternBlock (showChar ' ') showPattern a . 
>   showPunctuation RIGHT_BRACE .
>   showPatternBlocks showPattern b

> showPatternBlocks :: (a -> ShowS) -> PATTERNBLOCKS a -> ShowS
> showPatternBlocks _sa PATTERN_BLOCKSSTART = id
> showPatternBlocks sa (PATTERN_BLOCKSEXTENDDELIMOP a b) =
>   showPatternBlocks sa a . 
>   showPunctuation LEFT_BRACE .
>   showPatternBlock (showChar ' ') sa b .
>   showPunctuation RIGHT_BRACE

The implementation of the 'Pattern_ PATTERN' syntax interface is as follows.

> instance IsString PATTERN where
>   fromString s = PATTERN_PATH (fromString s) PATTERN_BLOCKSSTART

> instance Select_ PATTERN where
>   type Selects PATTERN = Either Self PATH
>   type Key PATTERN = IDENTIFIER
>   c #. i = PATTERN_PATH (c #. i) PATTERN_BLOCKSSTART

> instance Extend_ PATTERN where
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
>  :: PATTERNBLOCK a -> PATTERNBLOCK a
> proofPatternBlock = parsePatternBlock id

A parser for the grammar

> patternBlock :: Parser a -> Parser (PATTERNBLOCK a)
> patternBlock p = (do
>   a <- matchStmt p
>   b <- patternBlockStmt p
>   return (PATTERNBLOCK_STMT a b))
>   <|> return PATTERNBLOCK_END

> patternBlockStmt :: Parser a -> Parser (PATTERNBLOCK_STMT a)
> patternBlockStmt p =
>   patternBlockStmtSep <|> return PATTERNBLOCK_STMTEND
>   where
>     patternBlockStmtSep =
>       punctuation SEP_SEMICOLON >>
>       (PATTERNBLOCK_STMTSEP <$> patternBlock p)

The parse result can be interpreted as syntax via

> parsePatternBlock
>  :: PatternBlock_ r
>  => (a -> Rhs (Item r)) -> PATTERNBLOCK a -> r
> parsePatternBlock k b = fromList (toList b) where
>   toList PATTERNBLOCK_END = []
>   toList (PATTERNBLOCK_STMT a b) = case b of 
>     PATTERNBLOCK_STMTEND -> [parseMatchStmt k a]
>     PATTERNBLOCK_STMTSEP b -> parseMatchStmt k a : toList b

and printed via

> showPatternBlock
>  :: ShowS -> (a -> ShowS) -> PATTERNBLOCK a -> ShowS
> showPatternBlock wsep _sa PATTERNBLOCK_END = wsep
> showPatternBlock wsep sa (PATTERNBLOCK_STMT a b) =
>   wsep .
>   showMatchStmt sa a .
>   showPatternBlockStmt wsep sa b

> showPatternBlockStmt
>  :: ShowS -> (a -> ShowS) -> PATTERNBLOCK_STMT a -> ShowS
> showPatternBlockStmt _wsep _sa PATTERNBLOCK_STMTEND = id
> showPatternBlockStmt wsep sa (PATTERNBLOCK_STMTSEP b) =
>   showPunctuation SEP_SEMICOLON .
>   showPatternBlock wsep sa b

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
>   MATCHSTMT_IDENTIFIER IDENTIFIER FIELDS |
>   MATCHSTMT_FIELD SELECTOR (MATCHSTMT_FIELD a)
> data MATCHSTMT_FIELD a =
>   MATCHSTMT_FIELDEND |
>   MATCHSTMT_FIELDEQ a

> proofMatchStmt :: MATCHSTMT a -> MATCHSTMT a
> proofMatchStmt = parseMatchStmt id

A parser for the grammar is

> matchStmt :: Parser a -> Parser (MATCHSTMT a)
> matchStmt p = identifierFirst <|> fieldFirst where
>   identifierFirst = do
>     a <- identifier
>     b <- fields
>     return (MATCHSTMT_IDENTIFIER a b)
>   fieldFirst = do
>     a <- selector
>     b <- matchStmtField p
>     return (MATCHSTMT_FIELD a b)

> matchStmtField :: Parser a -> Parser (MATCHSTMT_FIELD a)
> matchStmtField p =
>   matchStmtEq <|> return MATCHSTMT_FIELDEND
>   where
>     matchStmtEq =
>       symbol "=" >> (MATCHSTMT_FIELDEQ <$> p)

For converting to Goat syntax

> parseMatchStmt
>  :: MatchStmt_ r => (a -> Rhs r) -> MATCHSTMT a -> r
> parseMatchStmt _k (MATCHSTMT_IDENTIFIER a b) =
>   parseMatchStmtIdentifier a b
>   where 
>     parseMatchStmtIdentifier
>      :: Path_ r => IDENTIFIER -> FIELDS -> r
>     parseMatchStmtIdentifier a FIELDS_START =
>       parseIdentifier a
>     parseMatchStmtIdentifier a (FIELDS_SELECTOP fs i) =
>       parseMatchStmtIdentifier a fs #. parseIdentifier i
> parseMatchStmt _k (MATCHSTMT_FIELD a MATCHSTMT_FIELDEND) =
>   parseSelector a
> parseMatchStmt k (MATCHSTMT_FIELD a (MATCHSTMT_FIELDEQ c)) =
>   parseSelector a #= k c

and for converting to a grammar string

> showMatchStmt :: (a -> ShowS) -> MATCHSTMT a -> ShowS
> showMatchStmt _sa (MATCHSTMT_IDENTIFIER a b) =
>   showIdentifier a .
>   showFields b
> showMatchStmt sa (MATCHSTMT_FIELD a b) =
>   showSelector a .
>   showMatchStmtField sa b

> showMatchStmtField :: (a -> ShowS) -> MATCHSTMT_FIELD a -> ShowS
> showMatchStmtField _sa MATCHSTMT_FIELDEND = id
> showMatchStmtField sa (MATCHSTMT_FIELDEQ a) =
>   showSymbolSpaced (SYMBOL "=") .
>   sa a

Goat syntax interface

> instance IsString (MATCHSTMT a) where
>   fromString s =
>     MATCHSTMT_IDENTIFIER (fromString s) FIELDS_START

> instance Select_ (MATCHSTMT a) where
>   type Selects (MATCHSTMT a) = Either Self PATH
>   type Key (MATCHSTMT a) = IDENTIFIER
>   p #. i = case p #. i of
>     PATH_IDENTIFIER a fs ->
>       MATCHSTMT_IDENTIFIER a fs
>
>     PATH_FIELD f fs ->
>       MATCHSTMT_FIELD (SELECTOR f fs) MATCHSTMT_FIELDEND

> instance Assign_ (MATCHSTMT a) where
>   type Lhs (MATCHSTMT a) = SELECTOR
>   type Rhs (MATCHSTMT a) = a
>   l #= r = MATCHSTMT_FIELD l (MATCHSTMT_FIELDEQ r)
