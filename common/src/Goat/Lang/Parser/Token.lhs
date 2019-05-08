Token
=====

> module Goat.Lang.Parser.Token where
>  
   
Identifier
----------

An *IDENTIFIER* begins with a *LETTER* ('a-Z'), 
optionally followed by a sequence of *ALPHANUMERIC* characters
, either a *LETTER* or *DIGIT* ('0-9').

    IDENTIFIER := LETTER [ALPHANUMERICS]
    LETTER := 'a' | ... | 'Z'
    ALPHANUMERICS := ALPHANUMERIC [ALPHANUMERICS]
    ALPHANUMERIC := LETTER | DIGIT

We can give a concrete representation that wraps Haskell's 'String' type, 
and implement an 'Identifier_' instance.

> newtype IDENTIFIER = IDENTIFIER String deriving IsString

with instance 'Identifier_ IDENTIFIER'.

> proofIDENTIFIER = test IDENTIFIER where
>   test :: Identifier_ a => a -> ()
>   test _ = ()

We can parse an identifier with

> identifier :: Parser IDENTIFIER
> identifier =
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

    SYMBOL := SYMBOLCHAR [SYMBOL]
    SYMBOLCHAR := '.' | '+' | '-' | '*' | '/' | '^' |
      '=' | '!' | '?' | '<' | '>' | '|' | '&' | '%' |
      '$' | '#' | '~' | '`'
     
We can concretely represent a symbol by the datatype below.

> newtype SYMBOL = SYMBOL (Char, Maybe SYMBOL)

We can parse a symbol with 

> symbol :: Parser SYMBOL
> symbol = do
>   a <- Parsec.oneOf ".+-*/^=!?<>|&%$#~`"
>   b <- Parsec.optionMaybe symbol
>   return (SYMBOL (a, b))

and show via

> showSymbol :: SYMBOL -> ShowS
> showSymbol (SYMBOL s) = showString s

Whitespace
----------

*WHITESPACE* in Goat is a sequence of *SPACE* characters or *COMMENTS*.
A *SPACE* is any Unicode space character or a '\t', '\n',
'\r', '\f', '\v' control character.
A *COMMENT* begins with a double slash ('//'),
and continues until a newline ('\n') or ('\r\n') or end of input.

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
> space = Parsec.space
>
> comment :: Parser COMMENT
> comment = do
>   Parsec.string "//"
>   s <- Parsec.manyTil Parsec.anyChar end
>   return (COMMENT s)
>   where
>     end = (Parsec.endOfLine $> ()) <|> Parsec.eof

and convert to Goat syntax via

> parseWhitespace :: Comment_ r => WHITESPACE -> r -> r
> parseWhitespace = go where
>   go (WHITESPACE (a, b)) c =
>    maybe id go b (either id parseComment a c)

> parseComment :: Comment_ r => COMMENT -> r -> r
> parseComment (COMMENT s) a = a #// s

and show the comment

> showWhitespace :: WHITESPACE -> ShowS
> showWhitespace (WHITESPACE (a, b)) =
>   either ' ' showComment a . either id showWhitespace b

> showComment :: COMMENT -> ShowS
> showComment (COMMENT s) = showString "//" . showString s .
>   showChar '\n'

NumberLiteral
-------------

In the Goat grammar a *NUMBERLITERAL* is either a *PREFIXBIN*,
*PREFIXOC*, *PREFIXHEX*, *PREFIXDEC*,
or an optional plus sign ('+') prefix followed by an *INTEGER*,
optionally followed by a *FRACTIONAL* and/or a *EXPONENT*,
a *FRACTIONAL* optionally followed by an *EXPONENT*,
or an *EXPONENT*.
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
An *EXPONENT* begins with an *ECHAR*, optionally followed by a *SIGN*, followed by an *INTEGER*.
An *ECHAR* is an 'e' or 'E'.
A *SIGN* is a plus character ('+') or a minus character ('-').

    NUMBERLITERAL :=
      PREFIXBIN | PREFIXOCT | PREFIXHEX | PREFIXDEC |
      ['+'] INTEGER [FRACTIONAL] [EXPONENT] |
      FRACTIONAL [EXPONENT] |
      EXPONENT
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
    EXPONENT := ECHAR [SIGN] INTEGER
    ECHAR := 'e' | 'E'
    SIGN := '+' | '-'
    
Below is a concrete representation as a Haskell datatype.

> data NUMBERLITERAL =
>   LITERAL_PREFIXBIN (PREFIXBIN, INTEGER) |
>   LITERAL_PREFIXOCT (PREFIXOCT, INTEGER) |
>   LITERAL_PREFIXHEX (PREFIXHEX, INTEGER) |
>   LITERAL_PREFIXDEC (PREFIXDEC, INTEGER) |
>   LITERAL_INTEGER
>    ( Maybe POSITIVESIGN, INTEGER, Maybe FRACTIONAL
>    , Maybe EXPONENT) |
>   LITERAL_FRACTIONAL (FRACTIONAL, Maybe EXPONENT) |
>   LITERAL_EXPONENT Exponent
> data PREFIXBIN = PREFIXBIN
> data PREFIXDEC = PREFIXDEC
> data PREFIXOCT = PREFIXOCT
> data PREFIXHEX = PREFIXHEX
> newtype INTEGER = INTEGER
>   (Char, Maybe (Maybe INTEGERSEP, INTEGER))
> data ISIGN = ISIGN_POSITIVE
> newtype FRACTIONAL = FRACTIONAL (DECIMALPOINT, INTEGER)
> newtype EXPONENT = EXPONENT (ECHAR, Maybe ESIGN, INTEGER)
> data ECHAR = ECHAR
> data ESIGN = ESIGN_POSITIVE | ESIGN_NEGATIVE

Parse

> numberLiteral :: Parser NUMBERLITERAL
> numberLiteral = prefixBinFirst <|>
>   prefixOctFirst <|>
>   prefixHexFirst <|>
>   prefixDecFirst <|>
>   plusIntegerFirst <|>
>   fractionalFirst <|>
>   exponentFirst <?>
>   "number literal"
>   where
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
>       d <- Parsec.optionMaybe exponent
>       return (LITERAL_INTEGER (a, b, c, d))
>     fractionalFirst = do
>       a <- fractional
>       b <- Parsec.optionMaybe exponent
>       return (LITERAL_FRACTIONAL (a, b))
>     exponentFirst = LITERAL_EXPONENT <$> exponent

> prefixBin :: Parser PREFIXBIN
> prefixBin = Parsec.string "0b" $> PREFIXBIN

> prefixOct :: Parser PREFIXOCT
> prefixOct = Parsec.string "0o" $> PREFIXOCT

> prefixHex :: Parser PREFIXHEX
> prefixHex = Parsec.string "0x" $> PREFIXHEX

> prefixDec :: Parser PREFIXDEC
> prefixDec = Parsec.string "0d" $> PREFIXDEC

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

> exponent :: Parser EXPONENT
> exponent = do
>   a <- echar
>   b <- Parsec.optionMaybe esign
>   c <- integer Parsec.digit
>   return (EXPONENT (a, b, c))

> echar :: Parser ECHAR
> echar = Parsec.oneOf "eE" $> ECHAR

> esign :: Parser ESIGN
> esign = (Parsec.char '+' $> ESIGN_POSITIVE) <|>
>   (Parsec.char '-' $> ESIGN_NEGATIVE)

To syntax

> parseNumberLiteral :: NumberLiteral_ r => NUMBERLITERAL -> r
> parseNumberLiteral = f where
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
>   f (LITERAL_PREFIXDEC (_, a)) = parseInteger (val 10) a 
>   f (LITERAL_INTEGER (_, a, b, c)) =
>     decFloat (parseInteger (val 10 . map read) a) b c
>   f (LITERAL_FRACTIONAL (a, b)) =
>     decFloat 0 (Just a) b
>   f (LITERAL_EXPONENT a) = decFloat 0 Nothing (Just a)
>
>   decFloat i Nothing Nothing = fromInteger i
>   decFloat i (Just a) Nothing =
>     fromRational (frac 0 i (parseFractional a))
>   decFloat i Nothing (Just b) = fromRational
>     (frac (parseExponential (val 10 . map read) b) i [])
>   decFloat i (Just a) (Just b) = fromRational
>     (frac (parseExponential (val 10 . map read) b) i
>       (parseFractional a))
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
>   map read (integerToList a)

> parseExponent :: (String -> Integer) -> EXPONENT -> Integer
> parseExponent digit2dig (EXPONENT (_, Just ESIGN_NEGATIVE, b)) =
>   -(parseInteger digit2dig b)
> parseExponent digit2dig (EXPONENT (_, _, b)) =
>   parseInteger digit2dig b

> integerToList :: INTEGER -> [Char]
> integerToList (INTEGER (a, b)) =
>   a : maybe [] (maybe [] integerToList . snd) b
  




-- | Parse a digit
digit :: Parser Int
digit = do
  d <- Parsec.digit
  return (read [d])
  

-- | Parse a list of digits
digits :: Parser [Int]
digits = digitString digit
 