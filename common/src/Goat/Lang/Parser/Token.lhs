Token
=====

> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> module Goat.Lang.Parser.Token where
> import Goat.Lang.Class
> import Text.Parsec.Text (Parser)
> import qualified Text.Parsec as Parsec
> import Text.Parsec ((<|>), (<?>))
> import Numeric (readHex, readOct)
> import Data.Ratio ((%))
> import Data.Foldable (foldl') 
> import Data.Functor (($>))

Whitespace
----------

*WHITESPACE* in Goat is a sequence of *SPACE* characters or *COMMENTS*.
A *SPACE* is any Unicode space character or a '\t', '\n',
'\r', '\f', '\v' control character.
A *COMMENT* begins with a double slash ('//'),
followed by a sequence of any non-*EOL* characters.
An *EOL* is a newline ('\n') or ('\r\n').

  WHITESPACE := SPACECOMMENT [WHITESPACE]
  SPACECOMMENT := SPACE | COMMENT 
  COMMENT := '//' [ANYLINE]
  ANYLINE := !EOL [ANYLINE]
  EOL := '\n' | '\r\n'

We can concretely represent a comment by wrapping a Haskell string.

> newtype WHITESPACE =
>   WHITESPACE (Either SPACE COMMENT, Maybe WHITESPACE)
> data SPACE = SPACE
> newtype COMMENT = COMMENT String

Parser

> whitespace :: Parser WHITESPACE
> whitespace = do
>   a <- (Left <$> space) <|> (Right <$> comment)
>   b <- Parsec.optionMaybe whitespace
>   return (WHITESPACE (a, b))
>
> space :: Parser SPACE
> space = Parsec.space $> SPACE
>
> comment :: Parser COMMENT
> comment = do
>   Parsec.string "//"
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
optionally followed by a sequence of *ALPHANUMERIC*s,
optionally followed by *WHITESPACE*.
An *ALPHANUMERIC* character is either a *LETTER* or *DIGIT*
('0-9').

    IDENTIFIER := LETTER [ALPHANUMERICS] [WHITESPACE]
    LETTER := 'a' | ... | 'Z'
    ALPHANUMERICS := ALPHANUMERIC [ALPHANUMERICS]
    ALPHANUMERIC := LETTER | DIGIT
    DIGIT := '0' | ... | '9'

We can give a concrete representation that wraps Haskell's 'String' type, 
and implement an 'Identifier_' instance.

> newtype IDENTIFIER = IDENTIFIER { getIdentifier :: String }
>   deriving IsString

We can parse an identifier with

> identifier :: Parser IDENTIFIER
> identifier =
>  (do
>    x <- Parsec.letter
>    xs <- Parsec.many Parsec.alphaNum
>    Parsec.optional whitespace
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

A *SYMBOL* is a *SYMBOLCHARS* optionally followed by *WHITESPACE*.
*SYMBOLCHARS* is a non-empty sequence of *SYMBOLCHAR*s.
A *SYMBOLCHAR* is one of a period ('.'),
a plus sign ('+'), a minus sign ('-'), an asterisk ('*'),
a slash ('/'), a caret ('^'), an equals sign ('='),
an exclamation mark ('!'), a question mark ('?'),
a less-than sign ('<'), a greater-than sign ('>'),
a bar ('|'), an and sign ('&'), a percent ('%'),
a dollar sign ('$'), a hash ('#'),  a tilde ('~'),
or a backtick ('`').

    SYMBOL := SYMBOLCHARS [WHITESPACE]
    SYMBOLCHARS := SYMBOLCHAR [SYMBOLCHARS]
    SYMBOLCHAR := '.' | '+' | '-' | '*' | '/' | '^' |
      '=' | '!' | '?' | '<' | '>' | '|' | '&' | '%' |
      '$' | '#' | '~' | '`'
     
We can concretely represent a symbol by the datatype below.

> newtype SYMBOL = SYMBOL { getSymbol :: String }

We can parse a symbol with 

> symbol :: Parser SYMBOL
> symbol = do
>   s <- Parsec.many1 (Parsec.oneOf ".+-*/^=!?<>|&%$#~`")
>   Parsec.optional whitespace
>   return (SYMBOL s)

and show via

> showSymbol :: SYMBOL -> ShowS
> showSymbol (SYMBOL s) = showString s

NumberLiteral
-------------

In the Goat grammar a *NUMBER* is a *NUMBERLITERAL*,
optionally followed by *WHITESPACE*.
A *NUMBERLITERAL* is either a *PREFIXBIN*,
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
An *EXPONENTIAL* begins with an *ECHAR*, optionally followed by a *SIGN*, followed by an *INTEGER*.
An *ECHAR* is an 'e' or 'E'.
A *SIGN* is a plus character ('+') or a minus character ('-').

    NUMBER := NUMBERLITERAL [WHITESPACE]
    NUMBERLITERAL :=
      PREFIXBIN | PREFIXOCT | PREFIXHEX | PREFIXDEC |
      UNPREFIXLITERAL
    UNPREFIXLITERAL :=
      ['+'] INTEGER [FRACTIONAL] [EXPONENTIAL] |
      FRACTIONAL [EXPONENTIAL] |
      EXPONENTIAL
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
    SIGN := '+' | '-'
    
Below is a concrete representation as a Haskell datatype.

> data NUMBER =
>   LITERAL_PREFIXBIN (PREFIXBIN, INTEGER) |
>   LITERAL_PREFIXOCT (PREFIXOCT, INTEGER) |
>   LITERAL_PREFIXHEX (PREFIXHEX, INTEGER) |
>   LITERAL_PREFIXDEC (PREFIXDEC, INTEGER) |
>    -- unprefix
>   LITERAL_INTEGER
>    ( Maybe ISIGN, INTEGER, Maybe FRACTIONAL
>    , Maybe EXPONENTIAL) |
>   LITERAL_FRACTIONAL (FRACTIONAL, Maybe EXPONENTIAL) |
>   LITERAL_EXPONENTIAL EXPONENTIAL
> data PREFIXBIN = PREFIXBIN
> data PREFIXDEC = PREFIXDEC
> data PREFIXOCT = PREFIXOCT
> data PREFIXHEX = PREFIXHEX
> newtype INTEGER = INTEGER
>   (Char, Maybe (Maybe INTEGERSEP, INTEGER))
> data ISIGN = ISIGN_POSITIVE
> data INTEGERSEP = INTEGERSEP
> newtype FRACTIONAL = FRACTIONAL (DECIMALPOINT, INTEGER)
> data DECIMALPOINT = DECIMALPOINT
> newtype EXPONENTIAL = EXPONENTIAL (ECHAR, Maybe ESIGN, INTEGER)
> data ECHAR = ECHAR
> data ESIGN = ESIGN_POSITIVE | ESIGN_NEGATIVE

Parse

> number :: Parser NUMBER
> number = numberLiteral <* Parsec.optional whitespace
>   where
>     numberLiteral = prefixBinFirst <|>
>       prefixOctFirst <|>
>       prefixHexFirst <|>
>       prefixDecFirst <|>
>       plusIntegerFirst <|>
>       fractionalFirst <|>
>       exponentialFirst <?>
>       "number literal"
>     prefixBinFirst = do
>       a <- Parsec.try prefixBin
>       b <- integer (Parsec.oneOf "01")
>       return (LITERAL_PREFIXBIN (a, b))
>     prefixOctFirst = do
>       a <- Parsec.try prefixOct
>       b <- integer Parsec.octDigit
>       return (LITERAL_PREFIXOCT (a, b))
>     prefixHexFirst = do
>       a <- Parsec.try prefixHex
>       b <- integer Parsec.hexDigit
>       return (LITERAL_PREFIXHEX (a, b))
>     prefixDecFirst = do
>       a <- Parsec.try prefixDec
>       b <- integer Parsec.digit
>       return (LITERAL_PREFIXDEC (a, b))
>     plusIntegerFirst = do
>       a <- Parsec.optionMaybe isign
>       b <- integer Parsec.digit
>       c <- Parsec.optionMaybe fractional
>       d <- Parsec.optionMaybe exponential
>       return (LITERAL_INTEGER (a, b, c, d))
>     fractionalFirst = do
>       a <- fractional
>       b <- Parsec.optionMaybe exponential
>       return (LITERAL_FRACTIONAL (a, b))
>     exponentialFirst = LITERAL_EXPONENTIAL <$> exponential

> prefixBin :: Parser PREFIXBIN
> prefixBin = Parsec.string "0b" $> PREFIXBIN

> prefixOct :: Parser PREFIXOCT
> prefixOct = Parsec.string "0o" $> PREFIXOCT

> prefixHex :: Parser PREFIXHEX
> prefixHex = Parsec.string "0x" $> PREFIXHEX

> prefixDec :: Parser PREFIXDEC
> prefixDec = Parsec.string "0d" $> PREFIXDEC

> isign :: Parser ISIGN
> isign = Parsec.char '+' $> ISIGN_POSITIVE

> integer :: Parser Char -> Parser INTEGER
> integer p = do
>   a <- p
>   b <- Parsec.optionMaybe
>     (do
>       a <- Parsec.optionMaybe integerSep 
>       b <- integer p
>       return (a, b))
>   return (INTEGER (a, b))

> integerSep :: Parser INTEGERSEP
> integerSep = Parsec.char '_' $> INTEGERSEP

> fractional :: Parser FRACTIONAL
> fractional = do
>   a <- decimalPoint
>   b <- integer Parsec.digit
>   return (FRACTIONAL (a, b))

> decimalPoint :: Parser DECIMALPOINT
> decimalPoint = Parsec.char '.' $> DECIMALPOINT

> exponential :: Parser EXPONENTIAL
> exponential = do
>   a <- echar
>   b <- Parsec.optionMaybe esign
>   c <- integer Parsec.digit
>   return (EXPONENTIAL (a, b, c))

> echar :: Parser ECHAR
> echar = Parsec.oneOf "eE" $> ECHAR

> esign :: Parser ESIGN
> esign = (Parsec.char '+' $> ESIGN_POSITIVE) <|>
>   (Parsec.char '-' $> ESIGN_NEGATIVE)

To syntax

> parseNumber :: Number_ r => NUMBER -> r
> parseNumber = f where
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
>   f (LITERAL_INTEGER (_, a, b, c)) =
>     decFloat (parseInteger (val 10 . digits) a) b c
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
> parseExponential digit2dig (EXPONENTIAL (_, Just ESIGN_NEGATIVE, b)) =
>   -(parseInteger digit2dig b)
> parseExponential digit2dig (EXPONENTIAL (_, _, b)) =
>   parseInteger digit2dig b

> integerToList :: INTEGER -> [Char]
> integerToList (INTEGER (a, b)) =
>   a : maybe [] (integerToList . snd) b

To show

> showNumber :: NUMBER -> ShowS
> showNumber (LITERAL_PREFIXBIN (a, b)) =
>   showPrefixBin a . showInteger b
> showNumber (LITERAL_PREFIXOCT (a, b)) =
>   showPrefixOct a . showInteger b
> showNumber (LITERAL_PREFIXDEC (a, b)) = 
>   showPrefixDec a . showInteger b
> showNumber (LITERAL_PREFIXHEX (a, b)) =
>   showPrefixHex a . showInteger b
> showNumber (LITERAL_INTEGER (a, b, c, d)) =
>   maybe id showIsign a . showInteger b .
>   maybe id showFractional c . maybe id showExponential d
> showNumber (LITERAL_FRACTIONAL (a, b) =
>   showFractional a . maybe id showExponential b
> showNumber (LITERAL_EXPONENTIAL a) = showExponential a

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

> showIsign :: ISIGN -> ShowS
> showIsign ISIGN_POSITIVE = showChar '+'

> showIntegerSep :: INTEGERSEP -> ShowS
> showIntegerSep INTEGERSEP = showChar '_'

> showFractional :: FRACTIONAL -> ShowS
> showFractional (FRACTIONAL (a, b)) = showDecimalPoint a .
>   showInteger b

> showDecimalPoint :: DECIMALPOINT -> ShowS
> showDecimalPoint DECIMALPOINT = showChar '.'

> showExponential :: EXPONENTIAL -> ShowS
> showExponential (EXPONENTIAL (a, b, c)) =
>   showEchar a . maybe id showEsign b . showInteger c

> showEchar :: ECHAR -> ShowS
> showEchar ECHAR = showChar 'e'

> showEsign :: ESIGN -> ShowS
> showESign ESIGN_POSITIVE = showChar '+'
> showESign ESIGN_NEGATIVE = showChar '-'

Syntax class instance

> instance Num NUMBER where
>   fromInteger i = LITERAL_INTEGER
>     (Nothing, integerToInteger i, Nothing, Nothing)
>   (+) = errorWithoutStackTrace "Num NUMBER: (+)"
>   (*) = errorWithoutStackTrace "Num NUMBER: (*)"
>   abs = errorWithoutStackTrace "Num NUMBER: abs"
>   negate = errorWithoutStackTrace "Num NUMBER: negate"
>   signum = errorWithoutStackTrace "Num NUMBER: signum"

> integerToInteger :: Integer -> INTEGER
> integerToInteger i = INTEGER (a, b)
>   where
>     a:as = show i
>     b = foldr (\ a s -> Just (INTEGER (a, s))) Nothing as

> instance Fractional NUMBER where
>   fromRational r = LITERAL_INTEGER
>     (Nothing, 
>     where
>       (i, f) = properFraction r
>   (/) = errorWithoutStackTrace "Fractional NUMBER: (/)"

Text
----

*TEXT* is a *TEXTFRAGMENT* optionally followed by *WHITESPACE*.
A *TEXTFRAGMENT* is a quotation mark ('"'),
optionally followed by *NOTQUOTES*,
ending with another quotation mark.
*NOTQUOTES* is a sequence of *NOTQUOTE* characters.
A *NOTQUOTE* character is any character that is not a quotation mark or backslash ('\'),
or an *ESCAPEDCHAR*.
An *ESCAPEDCHAR*  is either a double-backslash ('\\'),
or a literal '\n', a literal '\"', a literal '\r',
or a literal '\t'.

    TEXT := TEXTFRAGMENT [WHITESPACE]
    TEXTFRAGMENT := '"' [NOTQUOTES] '"'
    NOTQUOTES := NOTQUOTE [NOTQUOTES]
    NOTQUOTE := !QUOTESLASH | ESCAPEDCHAR
    QUOTESLASH = '"' | '\'
    ESCAPEDCHAR = '\\' | '\"' | '\n' | '\r' | '\t'
    
We can concretely represent *TEXT* by wrapping the regular Haskell string.

> newtype TEXT = TEXT (QUOTEMARK, String, QUOTEMARK)
> data QUOTEMARK = QUOTEMARK

Parse 

> text :: Parser TEXT
> text = textFragment <?> "text literal" <* whitespace
>   where 
>    textFragment = do
>      a <- quoteMark
>      b <- Parsec.many notQuote
>      c <- quoteMark
>      return (TEXT (a, b, c))

> quoteMark :: Parser QUOTEMARK
> quoteMark = Parsec.char '"' $> QUOTEMARK

> notQuote :: Parser Char
> notQuote = Parsec.noneOf "\"\\" <|> escapedChars

> escapedChars :: Parser Char
> escapedchars = do
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

> parseText :: Text_ r => TEXT -> r
> parseText (TEXT (_, a, _)) = quote_ a

To show

> showText :: TEXT -> ShowS
> showText (TEXT (a, b, c)) =
>   showQuoteMark a . showLitString b . showQuoteMark c

> showQuoteMark :: QUOTEMARK -> ShowS
> showQuoteMark QUOTEMARK = showChar '"'

> showLitString :: String -> ShowS
> showLitString []          s = s
> showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
> showLitString (c   : cs)  s = showLitChar c (showLitString cs s)

Syntax class instance

> class Text_ TEXT where
>   quote_ s = TEXT (QUOTEMARK, s, QUOTEMARK)
