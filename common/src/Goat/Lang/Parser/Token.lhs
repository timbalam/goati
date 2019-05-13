Token
=====

This module defines a parser in terms of a stream of tokens and source positions.

> {-# LANGUAGE GeneralizedNewtypeDeriving, LambdaCase #-}
> module Goat.Lang.Parser.Token where
> import Goat.Lang.Class
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))
> import qualified Data.Text as Text (Text)
> import Numeric (readHex, readOct)
> import Data.Char (intToDigit, showLitChar)
> import Data.Ratio ((%))
> import Data.Foldable (foldl') 
> import Data.Functor (($>))
> import Data.Scientific (Scientific, toDecimalDigits)


Parser
------

> type Parser = Parsec.Parsec [(Parsec.SourcePos, TOKEN)] ()
> type TokenParser = Parsec.Parsec Text.Text ()

> tokens :: TokenParser [(Parsec.SourcePos, TOKEN)]
> tokens = Parsec.many ((,) <$> Parsec.getPosition <*> token) 

> project :: (TOKEN -> Maybe a) -> Parser a
> project f = Parsec.token showTok posFromTok testTok where
>   showTok (pos, t) = showToken t ""
>   posFromTok (pos, t) = pos 
>   testTok (pos, t) = f t

> whitespace :: Parser WHITESPACE
> whitespace = project (\case
>   TOKEN_WHITESPACE s -> Just s; _ -> Nothing)
    
> project' :: (TOKEN -> Maybe a) -> Parser a
> project' f = project f <* whitespace

> numLiteral :: Parser NUMLITERAL
> numLiteral = project' (\case
>   TOKEN_NUMBER n -> Just n; _ -> Nothing)

> textLiteral :: Parser TEXTLITERAL
> textLiteral = project' (\case
>   TOKEN_TEXT t -> Just t; _ -> Nothing)

> identifier :: Parser IDENTIFIER
> identifier = project' (\case
>   TOKEN_IDENTIFIER i -> Just i; _ -> Nothing)

> symbol :: String -> Parser SYMBOL
> symbol a = project' (\case
>   TOKEN_SYMBOL s -> if getSymbol s == a then Just s else Nothing
>   _ -> Nothing)

> keyword :: String -> Parser KEYWORD
> keyword a = project' (\case
>   TOKEN_KEYWORD w
>     -> if getKeyword w == a then Just w else Nothing
>   _ -> Nothing)

> punctuation :: PUNCTUATION -> Parser PUNCTUATION
> punctuation a = project' (\case
>   TOKEN_PUNCTUATION u -> if u == a then Just u else Nothing
>   _ -> Nothing)

Token
-----

A *TOKEN* is either *WHITESPACE*, a *NUMLITERAL*,
a *TEXTLITERAL*, an *IDENTIFIER*, a *SYMBOL*, a *KEYWORD*,
or *PUNCTUATION*.
*PUNCTUATION* is a semi-colon (';'), a comma (','),
a left brace ('{'), a right brace ('}'), a left staple ('['),
a right staple (']'), a left paren ('('), or a right paren (')').

    TOKEN := WHITESPACE | NUMLITERAL | TEXTLITERAL |
      IDENTIFIER | SYMBOL | KEYWORD | PUNCTUATION
    PUNCTUATION := ';' | ',' | '{' | '}' | '[' | ']' |
      '(' | ')'

Concretely

> data TOKEN = TOKEN_WHITESPACE WHITESPACE |
>   TOKEN_NUMBER NUMLITERAL |
>   TOKEN_TEXT TEXTLITERAL |
>   TOKEN_IDENTIFIER IDENTIFIER |
>   TOKEN_SYMBOL SYMBOL |
>   TOKEN_KEYWORD KEYWORD |
>   TOKEN_PUNCTUATION PUNCTUATION
> data PUNCTUATION = SEP_COMMA | SEP_SEMICOLON |
>   LEFT_BRACE | RIGHT_BRACE | LEFT_STAPLE | RIGHT_STAPLE | 
>   LEFT_PAREN | RIGHT_PAREN
>   deriving Eq

To parse

> token :: TokenParser TOKEN
> token = (TOKEN_WHITESPACE <$> tokWhitespace) <|>
>   (TOKEN_NUMBER <$> tokNumLiteral) <|>
>   (TOKEN_TEXT <$> tokTextLiteral) <|>
>   (TOKEN_SYMBOL <$> tokSymbol) <|>
>   (TOKEN_IDENTIFIER <$> tokIdentifer) <|>
>   (TOKEN_KEYWORD <$> tokKeyword) <|> 
>   (TOKEN_PUNCTUATION <$> tokPunctuation) <?>
>   "token"

> tokPunctuation :: TokenParser PUNCTUATION
> tokPunctuation =
>   sepSemicolon <|>
>   sepComma <|>
>   leftBrace <|>
>   rightBrace <|>
>   leftStaple <|>
>   rightStaple <|>
>   leftParen <|>
>   rightParen 
>   where
>     sepSemicolon = Parsec.char ';' $> SEP_SEMICOLON
>     sepComma = Parsec.char ',' $> SEP_COMMA
>     leftBrace = Parsec.char '{' $> LEFT_BRACE
>     rightBrace = Parsec.char '}' $> RIGHT_BRACE
>     leftStaple = Parsec.char '[' $> LEFT_STAPLE
>     rightStaple = Parsec.char ']' $> RIGHT_STAPLE
>     leftParen = Parsec.char '(' $> LEFT_PAREN
>     rightParen = Parsec.char ')' $> RIGHT_PAREN

To show 

> showToken :: TOKEN -> ShowS
> showToken (TOKEN_WHITESPACE s) = showWhitespace s
> showToken (TOKEN_NUMBER n) = showNumLiteral n
> showToken (TOKEN_TEXT t) = showTextLiteral t
> showToken (TOKEN_IDENTIFIER i) = showIdentifier i
> showToken (TOKEN_SYMBOL b) = showSymbol b
> showToken (TOKEN_KEYWORD w) = showKeyword w
> showToken (TOKEN_PUNCTUATION p) = showPunctuation p 

> showPunctuation :: PUNCTUATION -> ShowS
> showPunctuation SEP_SEMICOLON = showChar ';'
> showPunctuation SEP_COMMA = showChar ','
> showPunctuation LEFT_BRACE = showChar '{'
> showPunctuation RIGHT_BRACE = showChar '}'
> showPunctuation LEFT_STAPLE = showChar '['
> showPunctuation RIGHT_STAPLE = showChar ']'
> showPunctuation LEFT_PAREN = showChar '('
> showPunctuation RIGHT_PAREN = showChar ')'

Whitespace
----------

*WHITESPACE* in Goat is a sequence of *SPACE* characters or *COMMENT*s.
A *SPACE* is any Unicode space character or a '\t', '\n',
'\r', '\f', '\v' control character.
A *COMMENT* begins with a double slash ('//'),
followed by a sequence of any non-*EOL* characters.
An *EOL* is a newline ('\n') or ('\r\n').

  WHITESPACE := (SPACE | COMMENT) [WHITESPACE]
  COMMENT := '//' [ANYLINE]
  ANYLINE := !EOL [ANYLINE]
  EOL := '\n' | '\r\n'

We can concretely represent a comment by wrapping a Haskell string.

> newtype WHITESPACE =
>   WHITESPACE (Either SPACE COMMENT, Maybe WHITESPACE)
> data SPACE = SPACE
> newtype COMMENT = COMMENT String

Parser

> tokWhitespace :: TokenParser WHITESPACE
> tokWhitespace = do
>   a <- (Left <$> space) <|> (Right <$> tokComment)
>   b <- Parsec.optionMaybe tokWhitespace
>   return (WHITESPACE (a, b))
>
> space :: TokenParser SPACE
> space = Parsec.space $> SPACE
>
> tokComment :: TokenParser COMMENT
> tokComment = do
>   Parsec.try (Parsec.string "//")
>   s <- Parsec.manyTill Parsec.anyChar end
>   return (COMMENT s)
>   where
>     end = (Parsec.endOfLine $> ()) <|> Parsec.eof

and convert to Goat syntax via

> parseWhitespace :: Comment_ r => WHITESPACE -> r -> r
> parseWhitespace = go where
>   go (WHITESPACE (a, b)) c =
>    maybe id go b (either (const id) parseComment a c)

> parseComment :: Comment_ r => COMMENT -> r -> r
> parseComment (COMMENT s) a = a #// s

and show the comment

> showWhitespace :: WHITESPACE -> ShowS
> showWhitespace (WHITESPACE (a, b)) =
>   either showSpace showComment a . maybe id showWhitespace b

> showSpace :: SPACE -> ShowS
> showSpace SPACE = showChar ' '

> showComment :: COMMENT -> ShowS
> showComment (COMMENT s) = showString "//" . showString s .
>   showChar '\n'
   
Identifier
----------

An *IDENTIFIER* begins with a *LETTER* ('a-Z'), 
optionally followed by *ALPHANUMBERICS*.
*ALPHANUMERICS*  is a sequence of either *LETTER*s or *DIGIT*s
('0-9').

    IDENTIFIER := LETTER [ALPHANUMERICS]
    LETTER := 'a' | ... | 'Z'
    ALPHANUMERICS := (LETTER | DIGIT) [ALPHANUMERICS]
    DIGIT := '0' | ... | '9'

We can give a concrete representation that wraps Haskell's 'String' type, 
and implement an 'Identifier_' instance.

> newtype IDENTIFIER = IDENTIFIER String deriving IsString
> getIdentifier (IDENTIFIER s) = s

We can parse an identifier with

> tokIdentifer :: TokenParser IDENTIFIER
> tokIdentifer =
>  (do
>    x <- Parsec.letter
>    xs <- Parsec.many Parsec.alphaNum
>    return (IDENTIFIER (x:xs))) <?>
>  "identifier"

The parse result can be converted to a type implementing the 'Identifier_' syntax interface

> parseIdentifier :: Identifier_ r => IDENTIFIER -> r 
> parseIdentifier (IDENTIFIER s) = fromString s

and converted back to a valid string

> showIdentifier :: IDENTIFIER -> ShowS
> showIdentifier (IDENTIFIER s) = showString s


Symbol
------

A *SYMBOL* is a non-empty sequence of *SYMBOLCHAR*s.
A *SYMBOLCHAR* is one of a period ('.'),
a plus sign ('+'), a minus sign ('-'), an asterisk ('*'),
a slash ('/'), a caret ('^'), an equals sign ('='),
an exclamation mark ('!'), a question mark ('?'),
a less-than sign ('<'), a greater-than sign ('>'),
a bar ('|'), an and sign ('&'), a percent ('%'),
a dollar sign ('$'), a hash ('#'),  a tilde ('~'),
or a backtick ('`').

    SYMBOL := SYMCHAR [SYMBOL]
    SYMCHAR := '.' | '+' | '-' | '*' | '/' | '^' |
      '=' | '!' | '?' | '<' | '>' | '|' | '&' | '%' |
      '$' | '#' | '~' | '`'
     
We can concretely represent a symbol by the datatype below.

> newtype SYMBOL = SYMBOL String
> getSymbol (SYMBOL s) = s

We can parse a symbol with 

> tokSymbol :: TokenParser SYMBOL
> tokSymbol = (do
>   s <- Parsec.many1 (Parsec.oneOf ".+-*/^=!?<>|&%$#~`")
>   return (SYMBOL s)) <?>
>   "symbol"

and show via

> showSymbol :: SYMBOL -> ShowS
> showSymbol (SYMBOL s) = showString s

> showSymbolSpaced :: SYMBOL -> ShowS
> showSymbolSpaced s = showChar ' ' . showSymbol s . showChar ' '

Num literal
-----------

In the Goat grammar a *NUMLITERAL* is either a *PREFIXBIN*,
*PREFIXOC*, *PREFIXHEX*, *PREFIXDEC*,
or an optional plus sign ('+') prefix followed by an *INTEGER*,
optionally followed by a *FRACTIONAL* and/or a *EXPONENTIAL*,
or a *FRACTIONAL* optionally followed by an *EXPONENTIAL*,
or an *EXPONENTIAL*.
A *PREFIXBIN* is a literal '0b' followed by *BINDIGITS*.
An *PREFIXOCT* is a literal '0o' followed by *OCTDIGITS*.
A *PREFIXHEX* is a literal '0x' followed by *HEXDIGITS*.
A *PREFIXDEC* is a literal '0d' followed by an *INTEGER*.
*BINDIGITS*, *OCTDIGITS*,
*HEXDIGITS* and *INTEGER* each are a literal digit
(respectively a *BINDIGIT*, *OCTDIGIT*, *HEXDIGIT* and *DIGIT*) 
optionally followed by an underscore ('_'),
optionally followed by a sequence of digits
(respectively *BINDIGITS*, *OCTDIGITS*, *HEXDIGITS*, *INTEGER*).
A *DECIMAL* is an optional plus sign ('+') followed by an *INTEGER*.
A *FRACTIONAL* begins with a period ('.') followed by an *INTEGER*.
An *EXPONENTIAL* begins with an *ECHAR*, optionally followed by a *ESIGN*,
followed by an *INTEGER*.
An *ECHAR* is an 'e' or 'E'.
An *ESIGN* is a plus character ('+') or a minus character ('-').

    NUMLITERAL :=
      PREFIXBIN | PREFIXOCT | PREFIXHEX | PREFIXDEC |
      UNPREFIXLITERAL
    UNPREFIXLITERAL :=
      [SIGN] INTEGER [FRACTIONAL] [EXPONENTIAL] |
      FRACTIONAL [EXPONENTIAL] |
      EXPONENTIAL
    SIGN := '+' | '-'
    PREFIXBIN := '0b' BINDIGITS
    BINDIGITS := BINDIGIT [['_'] BINDIGITS]
    BINDIGIT := '0' | '1'
    PREFIXOCT := '0o' OCTDIGITS
    OCTDIGITS := OCTDIGIT [['_'] OCTDIGITS]
    OCTDIGIT := '0' | ... | '7'
    PREFIXHEX := '0x' HEXDIGITS
    HEXDIGITS := HEXDIGIT [['_'] HEXDIGITS]
    HEXDIGIT := '0' | ... | '9' | 'a' | ... | 'f'
    PREFIXDEC := '0d' INTEGER
    INTEGER := DIGIT [['_'] INTEGER]
    DIGIT := '0' | ... | '9'
    FRACTIONAL := '.' INTEGER
    EXPONENTIAL := ECHAR [SIGN] INTEGER
    ECHAR := 'e' | 'E'
    
Below is a concrete representation as a Haskell datatype.

> data NUMLITERAL =
>   LITERAL_PREFIXBIN (PREFIXBIN, INTEGER) |
>   LITERAL_PREFIXOCT (PREFIXOCT, INTEGER) |
>   LITERAL_PREFIXHEX (PREFIXHEX, INTEGER) |
>   LITERAL_PREFIXDEC (PREFIXDEC, INTEGER) |
>    -- unprefix
>   LITERAL_INTEGER
>    ( Maybe SIGN, INTEGER, Maybe FRACTIONAL
>    , Maybe EXPONENTIAL) |
>   LITERAL_FRACTIONAL (FRACTIONAL, Maybe EXPONENTIAL) |
>   LITERAL_EXPONENTIAL EXPONENTIAL
> data PREFIXBIN = PREFIXBIN
> data PREFIXDEC = PREFIXDEC
> data PREFIXOCT = PREFIXOCT
> data PREFIXHEX = PREFIXHEX
> newtype INTEGER = INTEGER
>   (Char, Maybe (Maybe INTEGERSEP, INTEGER))
> data SIGN = SIGN_POSITIVE | SIGN_NEGATIVE
> data INTEGERSEP = INTEGERSEP
> newtype FRACTIONAL = FRACTIONAL (DECIMALPOINT, INTEGER)
> data DECIMALPOINT = DECIMALPOINT
> newtype EXPONENTIAL = EXPONENTIAL (ECHAR, Maybe SIGN, INTEGER)
> data ECHAR = ECHAR

Parse

> tokNumLiteral :: TokenParser NUMLITERAL
> tokNumLiteral = prefixBinFirst <|>
>   prefixOctFirst <|>
>   prefixHexFirst <|>
>   prefixDecFirst <|>
>   plusIntegerFirst <|>
>   fractionalFirst <|>
>   exponentialFirst <?>
>   "number literal"
>   where
>     prefixBinFirst = do
>       a <- prefixBin
>       b <- integer (Parsec.oneOf "01")
>       return (LITERAL_PREFIXBIN (a, b))
>     prefixOctFirst = do
>       a <- prefixOct
>       b <- integer Parsec.octDigit
>       return (LITERAL_PREFIXOCT (a, b))
>     prefixHexFirst = do
>       a <- prefixHex
>       b <- integer Parsec.hexDigit
>       return (LITERAL_PREFIXHEX (a, b))
>     prefixDecFirst = do
>       a <- prefixDec
>       b <- integer Parsec.digit
>       return (LITERAL_PREFIXDEC (a, b))
>     plusIntegerFirst = do
>       a <- Parsec.optionMaybe sign
>       b <- integer Parsec.digit
>       c <- Parsec.optionMaybe fractional
>       d <- Parsec.optionMaybe exponential
>       return (LITERAL_INTEGER (a, b, c, d))
>     fractionalFirst = do
>       a <- fractional
>       b <- Parsec.optionMaybe exponential
>       return (LITERAL_FRACTIONAL (a, b))
>     exponentialFirst = LITERAL_EXPONENTIAL <$> exponential

> prefixBin :: TokenParser PREFIXBIN
> prefixBin = Parsec.try (Parsec.string "0b") $> PREFIXBIN

> prefixOct :: TokenParser PREFIXOCT
> prefixOct = Parsec.try (Parsec.string "0o") $> PREFIXOCT

> prefixHex :: TokenParser PREFIXHEX
> prefixHex = Parsec.try (Parsec.string "0x") $> PREFIXHEX

> prefixDec :: TokenParser PREFIXDEC
> prefixDec = Parsec.try (Parsec.string "0d") $> PREFIXDEC

> integer :: TokenParser Char -> TokenParser INTEGER
> integer p = do
>   a <- p
>   b <- Parsec.optionMaybe
>     (do
>       a <- Parsec.optionMaybe integerSep 
>       b <- integer p
>       return (a, b))
>   return (INTEGER (a, b))

> integerSep :: TokenParser INTEGERSEP
> integerSep = Parsec.char '_' $> INTEGERSEP

> sign :: TokenParser SIGN
> sign = (Parsec.char '+' $> SIGN_POSITIVE) <|>
>   (Parsec.char '-' $> SIGN_NEGATIVE)

> fractional :: TokenParser FRACTIONAL
> fractional = do
>   a <- decimalPoint
>   b <- integer Parsec.digit
>   return (FRACTIONAL (a, b))

> decimalPoint :: TokenParser DECIMALPOINT
> decimalPoint = Parsec.char '.' $> DECIMALPOINT

> exponential :: TokenParser EXPONENTIAL
> exponential = do
>   a <- echar
>   b <- Parsec.optionMaybe sign
>   c <- integer Parsec.digit
>   return (EXPONENTIAL (a, b, c))

> echar :: TokenParser ECHAR
> echar = Parsec.oneOf "eE" $> ECHAR

To syntax

> parseNumLiteral :: NumLiteral_ r => NUMLITERAL -> r
> parseNumLiteral = f where
>   f (LITERAL_PREFIXBIN (_, a)) = parseInteger bin2dig a
>     where
>       bin2dig =
>         foldl'
>           (\digint x -> 2 * digint + (if x=='0' then 0 else 1))
>           0
>   f (LITERAL_PREFIXOCT (_, a)) =
>     parseInteger (\x -> fst (readOct x !! 0)) a
>   f (LITERAL_PREFIXHEX (_, a)) =
>     parseInteger (\x -> fst (readHex x !! 0)) a
>   f (LITERAL_PREFIXDEC (_, a)) =
>     parseInteger (val 10 . digits) a 
>   f (LITERAL_INTEGER (a, b, c, d)) = decFloat i c d where
>     i = case a of
>       Just SIGN_NEGATIVE -> -(parseInteger (val 10 . digits) b)
>       _                  -> parseInteger (val 10 . digits) b
>   f (LITERAL_FRACTIONAL (a, b)) =
>     decFloat 0 (Just a) b
>   f (LITERAL_EXPONENTIAL a) = decFloat 0 Nothing (Just a)
>
>   decFloat i Nothing Nothing = fromInteger i
>   decFloat i (Just a) Nothing =
>     fromRational (frac 0 i (parseFractional a))
>   decFloat i Nothing (Just b) = fromRational
>     (frac (parseExponential (val 10 . digits) b) i [])
>   decFloat i (Just a) (Just b) = fromRational
>     (frac (parseExponential (val 10 . digits) b) i
>       (parseFractional a))
>
>   digits :: [Char] -> [Int]
>   digits = map (read . pure)
>   
>   -- based on code from
>   -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#val
>   val :: Integer -> [Int] -> Integer
>   val base = foldl' go 0
>     where go r d = r * base + fromIntegral d
>        
>   -- based on code from
>   -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#fracExp
>   frac :: Integer -> Integer -> [Int] -> Rational
>   frac exp mant fs = if exp' < 0
>     then mant' % (10 ^ (-exp'))
>     else  fromInteger (mant' * 10^exp')
>     where
>       (exp', mant') = foldl' go (exp, mant) fs
>       go (e, r) d = (e-1, r * 10 + fromIntegral d)

> parseInteger
>  :: Num r => (String -> Integer) -> INTEGER -> r
> parseInteger digit2dig a =
>   fromInteger (digit2dig (integerToList a))

> parseFractional :: FRACTIONAL -> [Int]
> parseFractional (FRACTIONAL (_, a)) =
>   map (read . pure) (integerToList a)

> parseExponential
>  :: (String -> Integer) -> EXPONENTIAL -> Integer
> parseExponential digit2dig (EXPONENTIAL (_, a, b)) =
>   case a of
>     Just SIGN_NEGATIVE -> -(parseInteger digit2dig b)
>     _                  -> parseInteger digit2dig b

> integerToList :: INTEGER -> [Char]
> integerToList (INTEGER (a, b)) =
>   a : maybe [] (integerToList . snd) b

To show

> showNumLiteral :: NUMLITERAL -> ShowS
> showNumLiteral (LITERAL_PREFIXBIN (a, b)) =
>   showPrefixBin a . showInteger b
> showNumLiteral (LITERAL_PREFIXOCT (a, b)) =
>   showPrefixOct a . showInteger b
> showNumLiteral (LITERAL_PREFIXDEC (a, b)) = 
>   showPrefixDec a . showInteger b
> showNumLiteral (LITERAL_PREFIXHEX (a, b)) =
>   showPrefixHex a . showInteger b
> showNumLiteral (LITERAL_INTEGER (a, b, c, d)) =
>   maybe id showSign a . showInteger b .
>   maybe id showFractional c . maybe id showExponential d
> showNumLiteral (LITERAL_FRACTIONAL (a, b)) =
>   showFractional a . maybe id showExponential b
> showNumLiteral (LITERAL_EXPONENTIAL a) = showExponential a

> showPrefixBin :: PREFIXBIN -> ShowS
> showPrefixBin PREFIXBIN = showString "0b"

> showPrefixDec :: PREFIXDEC -> ShowS
> showPrefixDec PREFIXDEC = showString "0d"

> showPrefixOct :: PREFIXOCT -> ShowS
> showPrefixOct PREFIXOCT = showString "0o"

> showPrefixHex :: PREFIXHEX -> ShowS
> showPrefixHex PREFIXHEX = showString "0x"

> showInteger :: INTEGER -> ShowS
> showInteger (INTEGER (a, b)) =
>   showChar a . maybe id (\ (a, b) ->
>     maybe id showIntegerSep a . showInteger b) b

> showSign :: SIGN -> ShowS
> showSign SIGN_POSITIVE = showChar '+'
> showSign SIGN_NEGATIVE = showChar '-'

> showIntegerSep :: INTEGERSEP -> ShowS
> showIntegerSep INTEGERSEP = showChar '_'

> showFractional :: FRACTIONAL -> ShowS
> showFractional (FRACTIONAL (a, b)) = showDecimalPoint a .
>   showInteger b

> showDecimalPoint :: DECIMALPOINT -> ShowS
> showDecimalPoint DECIMALPOINT = showChar '.'

> showExponential :: EXPONENTIAL -> ShowS
> showExponential (EXPONENTIAL (a, b, c)) =
>   showEchar a . maybe id showSign b . showInteger c

> showEchar :: ECHAR -> ShowS
> showEchar ECHAR = showChar 'e'

Syntax class instance

> instance Num NUMLITERAL where
>   fromInteger i = LITERAL_INTEGER
>     (Nothing, digitsToInteger (show i), Nothing, Nothing)
>   (+) = error "Num NUMLITERAL: (+)"
>   (*) = error "Num NUMLITERAL: (*)"
>   abs = error "Num NUMLITERAL: abs"
>   negate = error "Num NUMLITERAL: negate"
>   signum = error "Num NUMLITERAL: signum"

> digitsToInteger :: String -> INTEGER
> digitsToInteger [] = error "digitsToInteger: []"
> digitsToInteger (a:as) = INTEGER (a, b) where
>   b = foldr (\ a s -> Just (Nothing, INTEGER (a, s))) Nothing as

> instance Fractional NUMLITERAL where
>   fromRational = rationalToNumLiteral
>   (/) = error "Fractional NUMLITERAL: (/)"

> rationalToNumLiteral :: Rational -> NUMLITERAL
> rationalToNumLiteral r = LITERAL_INTEGER
>   ( a, digitsToInteger b, Just frac, d )
>   where
>     frac = FRACTIONAL (DECIMALPOINT, digitsToInteger c)
>     (a, s) = case fromRational r of { s -> if s < 0 then
>       (Just SIGN_NEGATIVE, -s) else (Nothing, s) }
>     (is, e) = toDecimalDigits s
>     ds = map intToDigit is
>     (b, c, d) = if e < 0 || e > 7 then
>       partsExponent ds e else
>       partsFixed ds e
>
>     partsExponent (d:ds) e = ([d], ds, Just exp) where
>       exp = EXPONENTIAL (ECHAR, s, digitsToInteger (show pos))
>       (s, pos) = if e < 0 then 
>           (Just SIGN_NEGATIVE, -e) else
>           (Nothing, e)
>     partsExponent [] e =
>       error "rationalToNumLiteral/partsExponent: []"
>
>     -- based on code from
>     --https://hackage.haskell.org/package/scientific-0.3.6.2/docs/src/Data.Scientific.html#fmtAsFixed
>     partsFixed ds e
>       | e <= 0 = ("0", replicate (-e) '0' ++ ds, Nothing)
>       | otherwise = f e "" ds where
>           f 0 s rs     = (mk0 (reverse s), mk0 rs, Nothing)
>           f n s ""     = f (n-1) ('0':s) ""
>           f n s (r:rs) = f (n-1) (r:s)   rs
>           mk0 "" = "0"
>           mk0 ls = ls

Text
----

A *TEXTLITERAL* is a quotation mark ('"'),
optionally followed by *NOTQUOTES*,
ending with another quotation mark.
*NOTQUOTES* is a sequence of *NOTQUOTE* characters.
A *NOTQUOTE* character is any character that is not a quotation mark or backslash ('\'),
or an *ESCAPEDCHAR*.
An *ESCAPEDCHAR*  is either a double-backslash ('\\'),
or a literal '\n', a literal '\"', a literal '\r',
or a literal '\t'.

    TEXTLITERAL := '"' [NOTQUOTES] '"'
    NOTQUOTES := NOTQUOTE [NOTQUOTES]
    NOTQUOTE := !QUOTESLASH | ESCAPEDCHAR
    QUOTESLASH = '"' | '\'
    ESCAPEDCHAR = '\\' | '\"' | '\n' | '\r' | '\t'
    
We can concretely represent *TEXTLITERAL* by wrapping the regular Haskell string.

> newtype TEXTLITERAL = TEXTLITERAL (QUOTEMARK, String, QUOTEMARK)
> data QUOTEMARK = QUOTEMARK

Parse 

> tokTextLiteral :: TokenParser TEXTLITERAL
> tokTextLiteral = textFragment <?> "text literal"
>   where 
>    textFragment = do
>      a <- quoteMark
>      b <- Parsec.many notQuote
>      c <- quoteMark
>      return (TEXTLITERAL (a, b, c))

> quoteMark :: TokenParser QUOTEMARK
> quoteMark = Parsec.char '"' $> QUOTEMARK

> notQuote :: TokenParser Char
> notQuote = Parsec.noneOf "\"\\" <|> escapedChars

> escapedChars :: TokenParser Char
> escapedChars = do
>   Parsec.char '\\'
>   x <- Parsec.oneOf "\\\"nrt"
>   return
>     (case x of
>       '\\' -> x
>       '"' -> x
>       'n' -> '\n'
>       'r' -> '\r'
>       't' -> '\t')

To syntax 

> parseTextLiteral :: TextLiteral_ r => TEXTLITERAL -> r
> parseTextLiteral (TEXTLITERAL (_, a, _)) = quote_ a

To show

> showTextLiteral :: TEXTLITERAL -> ShowS
> showTextLiteral (TEXTLITERAL (a, b, c)) =
>   showQuoteMark a . showLitString b . showQuoteMark c

> showQuoteMark :: QUOTEMARK -> ShowS
> showQuoteMark QUOTEMARK = showChar '"'

> showLitString :: String -> ShowS
> showLitString []          s = s
> showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
> showLitString (c   : cs)  s = showLitChar c (showLitString cs s)

Syntax class instance

> instance TextLiteral_ TEXTLITERAL where
>   quote_ s = TEXTLITERAL (QUOTEMARK, s, QUOTEMARK)

Keyword
-------

A *KEYWORD* is an at-sign '@' followed by an *IDENTIFIER*.

    KEYWORD := '@' IDENTIFIER

Concretely

> newtype KEYWORD = KEYWORD_ATSIGN IDENTIFIER
> getKeyword (KEYWORD_ATSIGN a) = getIdentifier a

Parse

> tokKeyword :: TokenParser KEYWORD
> tokKeyword = (do
>   Parsec.char '@'
>   b <- tokIdentifer
>   return (KEYWORD_ATSIGN b)) <?>
>   "keyword"

Show

> showKeyword :: KEYWORD -> ShowS
> showKeyword (KEYWORD_ATSIGN b) =
>   showChar '@' . showIdentifier b
