> {-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
> module Goat.Lang.Parser.Pattern where
> import Goat.Lang.Parser.Token
> import Goat.Lang.Parser.Path
> import Goat.Lang.Class
> import Goat.Util ((...))
> import Data.Functor (($>))
> import Data.Void (Void)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))

Pattern
-------

A *PATTERN* can start with a *PATH*,
optionally followed by *PATTERNBLOCKS*.
Alternatively, it can be a *PATTERNBLOCK* delimited by braces
('{'), ('}'), optionally followed by *PATTERNBLOCKS*.
*PATTERNBLOCKS* is a sequence of brace-delimited *PATTERNBLOCK*s.

    PATTERNBLOCKS
     := ['{' PATTERNBLOCK '}' PATTERNBLOCKS]
    PATTERN
     := PATH PATTERNBLOCKS
      | '{' PATTERNBLOCK '}' PATTERNBLOCKS 
    
We can represent the grammar concretely with a datatype implementing the 'Pattern_' syntax interface.

> data PATTERNBLOCKS a
>   = PATTERN_BLOCKSSTART
>   | PATTERN_BLOCKSEXTENDDELIMOP
>       (PATTERNBLOCKS a) (PATTERNBLOCK a)
> data PATTERN
>   = PATTERN_PATH PATH (PATTERNBLOCKS PATTERN)
>   | PATTERN_BLOCKDELIM
>       (PATTERNBLOCK PATTERN)
>       (PATTERNBLOCKS PATTERN)

The grammar can be parsed with the following

> pattern :: Parser PATTERN
> pattern = pathfirst <|> blockfirst where
>   pathfirst
>     = do
>       a <- path
>       b <- patternBlocks pattern
>       return (PATTERN_PATH a b)
>   blockfirst
>     = do
>       a
>        <- Parsec.between
>             (punctuation LEFT_BRACE)
>             (punctuation RIGHT_BRACE)
>             (patternBlock pattern)
>       b <- patternBlocks pattern
>       return (PATTERN_BLOCKDELIM a b)

> patternBlocks
>  :: Parser p -> Parser (PATTERNBLOCKS p)
> patternBlocks p = go PATTERN_BLOCKSSTART where
>   go a
>     = (do
>       b
>        <- Parsec.between
>             (punctuation LEFT_BRACE)
>             (punctuation RIGHT_BRACE)
>             (patternBlock p)
>       go (PATTERN_BLOCKSEXTENDDELIMOP a b))
>    <|> return a

For converting grammar to syntax

> parsePattern :: Pattern_ r => PATTERN -> r
> parsePattern (PATTERN_PATH a b)
>   = parsePatternPath parsePattern a b
>   where
>   parsePatternPath
>    :: Pattern_ r
>    => (a -> r) -> PATH -> PATTERNBLOCKS a -> r
>   parsePatternPath _k a PATTERN_BLOCKSSTART
>     = parsePath a
>   parsePatternPath
>     k a (PATTERN_BLOCKSEXTENDDELIMOP bs b)
>     = parsePatternPath k a bs
>     # parsePatternBlock k b
>
> parsePattern (PATTERN_BLOCKDELIM a b)
>   = parsePatternBlock' parsePattern a b
>   where
>   parsePatternBlock'
>    :: Pattern_ r
>    => (a -> r)
>    -> PATTERNBLOCK a -> PATTERNBLOCKS a -> r
>   parsePatternBlock' k bb PATTERN_BLOCKSSTART
>     = parsePatternBlock k bb
>   
>   parsePatternBlock'
>     k bb (PATTERN_BLOCKSEXTENDDELIMOP bs b)
>     = parsePatternBlock' k bb bs
>     # parsePatternBlock k b

For showing

> showPattern :: PATTERN -> ShowS
> showPattern (PATTERN_PATH a b)
>   = showPath a . showPatternBlocks showPattern b
>
> showPattern (PATTERN_BLOCKDELIM a b)
>   = showPunctuation LEFT_BRACE
>   . showSpaced (showPatternBlock showPattern a)
>   . showPunctuation RIGHT_BRACE
>   . showPatternBlocks showPattern b

> showPatternBlocks
>  :: (a -> ShowS) -> PATTERNBLOCKS a -> ShowS
> showPatternBlocks _sa PATTERN_BLOCKSSTART = id
> showPatternBlocks
>   sa (PATTERN_BLOCKSEXTENDDELIMOP a b)
>   = showPatternBlocks sa a
>   . showPunctuation LEFT_BRACE
>   . showSpaced (showPatternBlock sa b)
>   . showPunctuation RIGHT_BRACE

The implementation of the 'Pattern_ PATTERN' syntax interface is as follows.

> data CanonPattern
>   = Path CanonPath
>   | PatternBlock [CanonMatchStmt CanonPattern]
>   | CanonPattern :## [CanonMatchStmt CanonPattern]
>   deriving (Eq, Show)

> proofPattern :: PATTERN -> CanonPattern
> proofPattern = parsePattern

> toPattern :: CanonPattern -> PATTERN
> toPattern (Path p)
>   = PATTERN_PATH (toPath p) PATTERN_BLOCKSSTART
> 
> toPattern (PatternBlock ms)
>   = PATTERN_BLOCKDELIM
>       (toPatternBlock toPattern ms)
>       PATTERN_BLOCKSSTART
> 
> toPattern (p :## ms)
>   = case toPattern p of
>     PATTERN_PATH p bs
>      -> PATTERN_PATH
>           p
>           (PATTERN_BLOCKSEXTENDDELIMOP
>              bs (toPatternBlock toPattern ms))
>     
>     PATTERN_BLOCKDELIM b bs
>      -> PATTERN_BLOCKDELIM
>           b
>           (PATTERN_BLOCKSEXTENDDELIMOP
>             bs (toPatternBlock toPattern ms))

Instances

> instance IsString CanonPattern where
>   fromString s = Path (fromString s)

> instance Select_ CanonPattern where
>   type Selects CanonPattern
>     = CanonPath_
>         (Either Self IDENTIFIER) IDENTIFIER
>   type Key CanonPattern = IDENTIFIER
>   (#.) = Path ... (#.)

> instance Extend_ CanonPattern where
>   type Extension CanonPattern
>     = [CanonMatchStmt CanonPattern]
>   (#) = (:##)

> instance IsList CanonPattern where
>   type Item CanonPattern
>     = CanonMatchStmt CanonPattern
>   fromList ms = PatternBlock ms
>   toList = error "IsList CanonPattern: toList"


Pattern block
-------------

A *PATTERNBLOCK* is a sequence of *MATCHSTMT*s,
separated and optionally terminated by semi-colons (';').

    PATTERNBLOCK := [MATCHSTMT [';' PATTERNBLOCK]]

Our concrete datatype representation implements the 'PatternBlock_' interface.

> data PATTERNBLOCK a
>   = PATTERNBLOCK_END
>   | PATTERNBLOCK_STMT
>       (MATCHSTMT a) (PATTERNBLOCK_STMT a)
> data PATTERNBLOCK_STMT a
>   = PATTERNBLOCK_STMTEND
>   | PATTERNBLOCK_STMTSEP (PATTERNBLOCK a)

A parser for the grammar

> patternBlock :: Parser a -> Parser (PATTERNBLOCK a)
> patternBlock p
>   = (do
>     a <- matchStmt p
>     b <- patternBlockStmt p
>     return (PATTERNBLOCK_STMT a b))
>  <|> return PATTERNBLOCK_END

> patternBlockStmt
>  :: Parser a -> Parser (PATTERNBLOCK_STMT a)
> patternBlockStmt p
>   = patternBlockStmtSep
>  <|> return PATTERNBLOCK_STMTEND
>   where
>   patternBlockStmtSep
>     = punctuation SEP_SEMICOLON
>    >> (PATTERNBLOCK_STMTSEP <$> patternBlock p)

The parse result can be interpreted as syntax via

> parsePatternBlock
>  :: PatternBlock_ r
>  => (a -> Rhs (Item r)) -> PATTERNBLOCK a -> r
> parsePatternBlock k b = fromList (toList b) where
>   toList PATTERNBLOCK_END = []
>   toList (PATTERNBLOCK_STMT a b)
>     = case b of 
>       PATTERNBLOCK_STMTEND
>        -> [parseMatchStmt k a]
>       
>       PATTERNBLOCK_STMTSEP b
>        -> parseMatchStmt k a : toList b

and printed via

> showPatternBlock
>  :: (a -> ShowS) -> PATTERNBLOCK a -> ShowS
> showPatternBlock _sa PATTERNBLOCK_END = id
> showPatternBlock sa (PATTERNBLOCK_STMT a b)
>   = showChar '\n'
>   . showMatchStmt sa a
>   . showPatternBlockStmt sa b

> showPatternBlockStmt
>  :: (a -> ShowS)
>  -> PATTERNBLOCK_STMT a -> ShowS
> showPatternBlockStmt _sa PATTERNBLOCK_STMTEND = id
> showPatternBlockStmt
>   sa (PATTERNBLOCK_STMTSEP b)
>   = showPunctuation SEP_SEMICOLON
>   . showPatternBlock sa b

> showSpaced :: ShowS -> ShowS
> showSpaced shows s = unwords (lines (shows ""))++s

Conversion from a canonical representation implementation of Goat syntax

> toPatternBlock
>  :: (a -> b)
>  -> [CanonMatchStmt a] -> PATTERNBLOCK b
> toPatternBlock f [] = PATTERNBLOCK_END
> toPatternBlock f (s:ss)
>   = PATTERNBLOCK_STMT
>      (toMatchStmt f s)
>       (PATTERNBLOCK_STMTSEP (toPatternBlock f ss))

> proofPatternBlock
>  :: PATTERNBLOCK a -> [CanonMatchStmt a]
> proofPatternBlock = parsePatternBlock id

Match Statement
---------------

The grammar defines multiple forms for a *MATCHSTMT*.
It can be an *IDENTIFIER* followed by *FIELDS*,
or else a *SELECTOR*,
optionally followed by an equals sign ('=') and a *PATTERN*.

    MATCHSTMT
     := IDENTIFIER FIELDS
      | SELECTOR ['=' PATTERN]

Our concrete representation with demonstrated 'MatchStmt_' instance follows.

> data MATCHSTMT a
>   = MATCHSTMT_IDENTIFIER IDENTIFIER FIELDS
>   | MATCHSTMT_FIELD SELECTOR (MATCHSTMT_FIELD a)
> data MATCHSTMT_FIELD a
>   = MATCHSTMT_END | MATCHSTMT_EQ a

A parser for the grammar is

> matchStmt :: Parser a -> Parser (MATCHSTMT a)
> matchStmt p = identifierFirst <|> fieldFirst where
>   identifierFirst
>     = do
>       a <- identifier
>       b <- fields
>       return (MATCHSTMT_IDENTIFIER a b)
>   fieldFirst
>     = do
>       a <- selector
>       b <- matchStmtField p
>       return (MATCHSTMT_FIELD a b)

> matchStmtField
>  :: Parser a -> Parser (MATCHSTMT_FIELD a)
> matchStmtField p
>   = matchStmtEq <|> return MATCHSTMT_END
>   where
>   matchStmtEq
>     = symbol "=" >> (MATCHSTMT_EQ <$> p)

For converting to Goat syntax

> parseMatchStmt
>  :: MatchStmt_ r
>  => (a -> Rhs r) -> MATCHSTMT a -> r
> parseMatchStmt _k (MATCHSTMT_IDENTIFIER a b)
>   = parseMatchStmtIdentifier a b
>   where 
>   parseMatchStmtIdentifier
>    :: Path_ r => IDENTIFIER -> FIELDS -> r
>   parseMatchStmtIdentifier a FIELDS_START
>     = parseIdentifier a
>   
>   parseMatchStmtIdentifier
>     a (FIELDS_SELECTOP fs i)
>     = parseMatchStmtIdentifier a fs
>     #. parseIdentifier i
> 
> parseMatchStmt
>   _k (MATCHSTMT_FIELD a MATCHSTMT_END)
>   = parseSelector a
> 
> parseMatchStmt
>   k (MATCHSTMT_FIELD a (MATCHSTMT_EQ c))
>   = parseSelector a #= k c

and for converting to a grammar string

> showMatchStmt
>  :: (a -> ShowS) -> MATCHSTMT a -> ShowS
> showMatchStmt _sa (MATCHSTMT_IDENTIFIER a b)
>   = showIdentifier a . showFields b
> showMatchStmt sa (MATCHSTMT_FIELD a b)
>   = showSelector a . showMatchStmtField sa b

> showMatchStmtField
>  :: (a -> ShowS) -> MATCHSTMT_FIELD a -> ShowS
> showMatchStmtField _sa MATCHSTMT_END = id
> showMatchStmtField sa (MATCHSTMT_EQ a)
>   = showSymbolSpaced "=" . sa a

We define a canonical representation for implementing the Goat syntax interface

> data CanonMatchStmt a
>   = MatchPun CanonPath | CanonSelector :##= a
>   deriving (Eq, Show)

> proofMatchStmt :: MATCHSTMT a -> CanonMatchStmt a
> proofMatchStmt = parseMatchStmt id

and conversion to our grammar types.

> toMatchStmt
>  :: (a -> b) -> CanonMatchStmt a -> MATCHSTMT b
> toMatchStmt _f (MatchPun p)
>   = case toPath p of
>     PATH_IDENTIFIER i fs
>      -> MATCHSTMT_IDENTIFIER i fs
>     
>     PATH_FIELD ff fs
>      -> MATCHSTMT_FIELD
>           (SELECTOR ff fs) MATCHSTMT_END
> 
> toMatchStmt f (s :##= p)
>   = MATCHSTMT_FIELD
>       (toSelector s) (MATCHSTMT_EQ (f p))

The canonical representation requires the following instances

> instance IsString (CanonMatchStmt a) where
>   fromString s = MatchPun (fromString s)

> instance Select_ (CanonMatchStmt a) where
>   type Selects (CanonMatchStmt a)
>     = CanonPath_
>         (Either Self IDENTIFIER) IDENTIFIER
>   type Key (CanonMatchStmt a) = IDENTIFIER
>   (#.) = MatchPun ... (#.)

> instance Assign_ (CanonMatchStmt a) where
>   type Lhs (CanonMatchStmt a) = CanonSelector
>   type Rhs (CanonMatchStmt a) = a
>   (#=) = (:##=)
