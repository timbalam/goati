{-
Token
=====

This module defines a parser in terms of a stream of tokens and source positions.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving, LambdaCase #-}
module Goat.Lang.Parser.Token where
import Goat.Lang.Class
import Goat.Util ((...))
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import qualified Data.Text as Text (Text)
import Numeric (readHex, readOct)
import Data.Char (intToDigit, showLitChar)
import Data.Ratio ((%))
import Data.Foldable (foldl') 
import Data.Functor (($>))
import Data.Scientific (Scientific, toDecimalDigits)

{-
Parser
------

-}

type Parser = Parsec.Parsec [(Parsec.SourcePos, TOKEN)] ()
type TokenParser = Parsec.Parsec Text.Text ()

tokens :: TokenParser [(Parsec.SourcePos, TOKEN)]
tokens = Parsec.many ((,) <$> Parsec.getPosition <*> token) 

project :: (TOKEN -> Maybe a) -> Parser a
project f = Parsec.token showTok posFromTok testTok where
  showTok (pos, t) = showToken t ""
  posFromTok (pos, t) = pos 
  testTok (pos, t) = f t

anyToken :: Parser TOKEN
anyToken = project Just

whitespace :: Parser WHITESPACE
whitespace = project (\case
  TOKEN_WHITESPACE s -> Just s; _ -> Nothing)
    
project' :: (TOKEN -> Maybe a) -> Parser a
project' f = project f <* whitespace

numLiteral :: Parser NUMLITERAL
numLiteral = project' (\case
  TOKEN_NUMBER n -> Just n; _ -> Nothing)

textLiteral :: Parser TEXTLITERAL
textLiteral = project' (\case
  TOKEN_TEXT t -> Just t; _ -> Nothing)

identifier :: Parser IDENTIFIER
identifier = project' (\case
  TOKEN_IDENTIFIER i -> Just i; _ -> Nothing)

symbol :: String -> Parser SYMBOL
symbol a = project' (\case
  TOKEN_SYMBOL s -> if getSymbol s == a then Just s else Nothing
  _ -> Nothing)

keyword :: String -> Parser KEYWORD
keyword a = project' (\case
  TOKEN_KEYWORD w
    -> if getKeyword w == a then Just w else Nothing
  _ -> Nothing)

punctuation :: PUNCTUATION -> Parser PUNCTUATION
punctuation a = project' (\case
  TOKEN_PUNCTUATION u -> if u == a then Just u else Nothing
  _ -> Nothing)

eof :: Parser ()
eof =
  Parsec.try
    ((do
      c <- Parsec.try anyToken
      Parsec.unexpected (showToken c ""))
        <|> return ())
    <?> "end of input"

{-
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
-}

-- Concretely

data TOKEN = TOKEN_WHITESPACE WHITESPACE |
  TOKEN_NUMBER NUMLITERAL |
  TOKEN_TEXT TEXTLITERAL |
  TOKEN_IDENTIFIER IDENTIFIER |
  TOKEN_SYMBOL SYMBOL |
  TOKEN_KEYWORD KEYWORD |
  TOKEN_PUNCTUATION PUNCTUATION
data PUNCTUATION = SEP_COMMA | SEP_SEMICOLON |
  LEFT_BRACE | RIGHT_BRACE | LEFT_STAPLE | RIGHT_STAPLE | 
  LEFT_PAREN | RIGHT_PAREN
  deriving Eq

-- To parse

token :: TokenParser TOKEN
token = (TOKEN_WHITESPACE <$> tokWhitespace) <|>
  (TOKEN_NUMBER <$> tokNumLiteral) <|>
  (TOKEN_TEXT <$> tokTextLiteral) <|>
  (TOKEN_SYMBOL <$> tokSymbol) <|>
  (TOKEN_IDENTIFIER <$> tokIdentifer) <|>
  (TOKEN_KEYWORD <$> tokKeyword) <|> 
  (TOKEN_PUNCTUATION <$> tokPunctuation) <?>
  "token"

tokPunctuation :: TokenParser PUNCTUATION
tokPunctuation =
  sepSemicolon <|>
  sepComma <|>
  leftBrace <|>
  rightBrace <|>
  leftStaple <|>
  rightStaple <|>
  leftParen <|>
  rightParen 
  where
    sepSemicolon = Parsec.char ';' $> SEP_SEMICOLON
    sepComma = Parsec.char ',' $> SEP_COMMA
    leftBrace = Parsec.char '{' $> LEFT_BRACE
    rightBrace = Parsec.char '}' $> RIGHT_BRACE
    leftStaple = Parsec.char '[' $> LEFT_STAPLE
    rightStaple = Parsec.char ']' $> RIGHT_STAPLE
    leftParen = Parsec.char '(' $> LEFT_PAREN
    rightParen = Parsec.char ')' $> RIGHT_PAREN

-- To show 

showToken :: TOKEN -> ShowS
showToken (TOKEN_WHITESPACE s) = showWhitespace s
showToken (TOKEN_NUMBER n) = showNumLiteral n
showToken (TOKEN_TEXT t) = showTextLiteral t
showToken (TOKEN_IDENTIFIER i) = showIdentifier i
showToken (TOKEN_SYMBOL b) = showSymbol (getSymbol b)
showToken (TOKEN_KEYWORD w) = showKeyword (getKeyword w)
showToken (TOKEN_PUNCTUATION p) = showPunctuation p 

showPunctuation :: PUNCTUATION -> ShowS
showPunctuation SEP_SEMICOLON = showChar ';'
showPunctuation SEP_COMMA = showChar ','
showPunctuation LEFT_BRACE = showChar '{'
showPunctuation RIGHT_BRACE = showChar '}'
showPunctuation LEFT_STAPLE = showChar '['
showPunctuation RIGHT_STAPLE = showChar ']'
showPunctuation LEFT_PAREN = showChar '('
showPunctuation RIGHT_PAREN = showChar ')'

{-
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
-}

-- We can concretely represent a comment by wrapping a Haskell string.

newtype WHITESPACE =
  WHITESPACE (Either SPACE COMMENT, Maybe WHITESPACE)
data SPACE = SPACE
newtype COMMENT = COMMENT String

-- Parser

tokWhitespace :: TokenParser WHITESPACE
tokWhitespace = do
  a <- (Left <$> space) <|> (Right <$> tokComment)
  b <- Parsec.optionMaybe tokWhitespace
  return (WHITESPACE (a, b))

space :: TokenParser SPACE
space = Parsec.space $> SPACE

tokComment :: TokenParser COMMENT
tokComment = do
  Parsec.try (Parsec.string "//")
  s <- Parsec.manyTill Parsec.anyChar end
  return (COMMENT s)
  where
    end = (Parsec.endOfLine $> ()) <|> Parsec.eof

-- and convert to Goat syntax via

parseWhitespace :: Comment_ r => WHITESPACE -> r -> r
parseWhitespace = go where
  go (WHITESPACE (a, b)) c =
   maybe id go b (either (const id) parseComment a c)

parseComment :: Comment_ r => COMMENT -> r -> r
parseComment (COMMENT s) a = a #// s

-- and show the comment

showWhitespace :: WHITESPACE -> ShowS
showWhitespace (WHITESPACE (a, b)) =
  either showSpace showComment a . maybe id showWhitespace b

showSpace :: SPACE -> ShowS
showSpace SPACE = showChar ' '

showComment :: COMMENT -> ShowS
showComment (COMMENT s) = showString "//" . showString s .
  showChar '\n'

{- 
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
-}

-- We can give a concrete representation that wraps Haskell's 'String' type, 
-- and implement an 'Identifier_' instance.

newtype IDENTIFIER = IDENTIFIER String deriving IsString
getIdentifier (IDENTIFIER s) = s

-- We can parse an identifier with

tokIdentifer :: TokenParser IDENTIFIER
tokIdentifer =
 (do
   x <- Parsec.letter
   xs <- Parsec.many Parsec.alphaNum
   return (IDENTIFIER (x:xs))) <?>
 "identifier"

-- The parse result can be converted to a type implementing the 
-- 'Identifier_' syntax interface

parseIdentifier :: Identifier_ r => IDENTIFIER -> r 
parseIdentifier (IDENTIFIER s) = fromString s

-- and converted back to a valid string

showIdentifier :: IDENTIFIER -> ShowS
showIdentifier (IDENTIFIER s) = showString s

{-
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
-}
     
-- We can concretely represent a symbol by the datatype below.

newtype SYMBOL = SYMBOL String
getSymbol (SYMBOL s) = s

-- We can parse a symbol with 

tokSymbol :: TokenParser SYMBOL
tokSymbol = (do
  s <- Parsec.many1 (Parsec.oneOf ".+-*/^=!?<>|&%$#~`")
  return (SYMBOL s)) <?>
  "symbol"

-- and show via

showSymbol :: String -> ShowS
showSymbol s = showString s

showSymbolSpaced :: String -> ShowS
showSymbolSpaced s = showChar ' ' . showString s . showChar ' '

{-
Num literal
-----------

In the Goat grammar a *NUMLITERAL* is either a literal '0b' 
followed by *BINDIGITS*,
a literal '0o' followed by *OCTDIGITS*,
a literal '0x' followed by *HEXDIGITS*,
a literal '0d' followed by an *INTEGER*,
an optional *sign* followed by an *INTEGER*,
optionally followed by a *FRACTIONAL*,
or a period ('.')
followed by an *INTEGER* optionally followed by an *EXPONENTIAL*.
*BINDIGITS*, *OCTDIGITS*,
*HEXDIGITS* and *INTEGER* each are a literal digit
(respectively a *BINDIGIT*, *OCTDIGIT*, *HEXDIGIT* and *DIGIT*) 
optionally followed by an underscore ('_'),
optionally followed by a sequence of digits
(respectively *BINDIGITS*, *OCTDIGITS*, *HEXDIGITS*, *INTEGER*).
A *FRACTIONAL* is either a period ('.')
optionally followed by an *INTEGER*,
optionally followed an *EXPONENTIAL*,
or an *EXPONENTIAL*
An *EXPONENTIAL* begins with an *ECHAR*,
optionally followed by a *ESIGN*,
followed by an *INTEGER*.
An *ECHAR* is an 'e' or 'E'.
An *SIGN* is a plus character ('+') or a minus character ('-').

    NUMLITERAL :=
      '0b' BINDIGITS | '0o' OCTDIGITS |
      '0x' HEXDIGITS | '0d' INTEGER |
      [SIGN] INTEGER [FRACTIONAL] |
      '.' INTEGER [EXPONENTIAL]
    SIGN := '+' | '-'
    BINDIGITS := BINDIGIT [['_'] BINDIGITS]
    BINDIGIT := '0' | '1'
    OCTDIGITS := OCTDIGIT [['_'] OCTDIGITS]
    OCTDIGIT := '0' | ... | '7'
    HEXDIGITS := HEXDIGIT [['_'] HEXDIGITS]
    HEXDIGIT := '0' | ... | '9' | 'a' | ... | 'f'
    INTEGER := DIGIT [['_'] INTEGER]
    DIGIT := '0' | ... | '9'
    FRACTIONAL := '.' [INTEGER [EXPONENTIAL]] | EXPONENTIAL
    EXPONENTIAL := ECHAR [SIGN] INTEGER
    ECHAR := 'e' | 'E'
-}

-- Below is a concrete representation as a Haskell datatype.

data NUMLITERAL =
  LITERAL_PREFIXBIN INTEGER |
  LITERAL_PREFIXOCT INTEGER |
  LITERAL_PREFIXHEX INTEGER |
  LITERAL_PREFIXDEC INTEGER |
   -- unprefix
  LITERAL_INTEGER (Maybe SIGN) INTEGER (Maybe FRACTIONAL) |
  LITERAL_PERIOD INTEGER (Maybe EXPONENTIAL)
data FRACTIONAL =
  FRACTIONAL_PERIOD FRACTIONAL_PERIOD |
  FRACTIONAL_EXPONENTIAL EXPONENTIAL
data FRACTIONAL_PERIOD =
  FRACTIONAL_END |
  FRACTIONAL_INTEGER INTEGER (Maybe EXPONENTIAL)
data INTEGER = INTEGER_CHAR Char INTEGER_CHAR
data INTEGER_CHAR =
  INTEGER_END | 
  INTEGER_UNDERSCORESEP INTEGER |
  INTEGER INTEGER
data SIGN = SIGN_POSITIVE | SIGN_NEGATIVE
data EXPONENTIAL = EXPONENTIAL_ECHAR (Maybe SIGN) INTEGER

-- Parse

tokNumLiteral :: TokenParser NUMLITERAL
tokNumLiteral = prefixBinNext <|>
  prefixOctNext <|>
  prefixHexNext <|>
  prefixDecNext <|>
  integerNext <|>
  fractionalNext <?>
  "number literal"
  where
    prefixBinNext =
      Parsec.try (Parsec.string "0b") >>
      LITERAL_PREFIXBIN <$> integer (Parsec.oneOf "01")
    prefixOctNext = 
      Parsec.try (Parsec.string "0o") >>
      LITERAL_PREFIXOCT <$> integer Parsec.octDigit
    prefixHexNext =
      Parsec.try (Parsec.string "0x") >>
      LITERAL_PREFIXHEX <$> integer Parsec.hexDigit
    prefixDecNext = 
      Parsec.try (Parsec.string "0d") >>
      LITERAL_PREFIXDEC <$> integer Parsec.digit
    integerNext = do
      a <- Parsec.optionMaybe sign
      b <- integer Parsec.digit
      c <- Parsec.optionMaybe fractional
      return (LITERAL_INTEGER a b c)
    fractionalNext = do
      Parsec.char '.'
      a <- integer Parsec.digit
      b <- Parsec.optionMaybe exponential
      return (LITERAL_PERIOD a b)

fractional :: TokenParser FRACTIONAL
fractional = fractionalNext <|> exponentialNext
  where
    fractionalNext =
      Parsec.char '.' >>
      FRACTIONAL_PERIOD <$> fractionalPeriod
    exponentialNext = FRACTIONAL_EXPONENTIAL <$> exponential
  
fractionalPeriod :: TokenParser FRACTIONAL_PERIOD
fractionalPeriod = (do
  a <- integer Parsec.digit
  b <- Parsec.optionMaybe exponential
  return (FRACTIONAL_INTEGER a b)) <|>
  return FRACTIONAL_END

integer :: TokenParser Char -> TokenParser INTEGER
integer p = do
  a <- p
  b <- integerChar p
  return (INTEGER_CHAR a b)
  where
    integerChar :: TokenParser Char -> TokenParser INTEGER_CHAR
    integerChar p =
      underscoreNext <|> charNext <|> return INTEGER_END
      where
        underscoreNext =
          Parsec.char '_' >>
          INTEGER_UNDERSCORESEP <$> integer p
        charNext = INTEGER <$> integer p

sign :: TokenParser SIGN
sign = (Parsec.char '+' $> SIGN_POSITIVE) <|>
  (Parsec.char '-' $> SIGN_NEGATIVE)

exponential :: TokenParser EXPONENTIAL
exponential = do
  Parsec.oneOf "eE"
  a <- Parsec.optionMaybe sign
  b <- integer Parsec.digit
  return (EXPONENTIAL_ECHAR a b)

-- To syntax

parseNumLiteral :: NumLiteral_ r => NUMLITERAL -> r
parseNumLiteral = \case
  LITERAL_PREFIXBIN a -> parseInteger bin2dig a
  
  LITERAL_PREFIXOCT a ->
    parseInteger (\x -> fst (readOct x !! 0)) a
  
  LITERAL_PREFIXHEX a ->
    parseInteger (\x -> fst (readHex x !! 0)) a
  
  LITERAL_PREFIXDEC a ->
    parseInteger (val 10 . digits) a
  
  LITERAL_INTEGER a b c ->
    let
      i =
        case a of
          Just SIGN_NEGATIVE ->
            -(parseInteger (val 10 . digits) b)
          
          _ ->
            parseInteger (val 10 . digits) b
    in 
      maybe (fromInteger i) (decFloat i) c
  
  LITERAL_PERIOD a b ->
    decFloat 0 (FRACTIONAL_PERIOD (FRACTIONAL_INTEGER a b))
  where
    bin2dig =
      foldl'
        (\digint x -> 2 * digint + (if x=='0' then 0 else 1))
        0
    
    decFloat i (FRACTIONAL_PERIOD b) =
      case b of
        FRACTIONAL_END -> 
          fromRational (frac 0 i [])
        
        FRACTIONAL_INTEGER a Nothing ->
          fromRational (frac 0 i (digits (integerToList a)))
        
        FRACTIONAL_INTEGER a (Just b) ->
          fromRational
            (frac
              (parseExponential (val 10 . digits) b)
              i
              (digits (integerToList a)))
        
    decFloat i (FRACTIONAL_EXPONENTIAL b) =
      fromRational
        (frac (parseExponential (val 10 . digits) b) i [])
    
    digits :: [Char] -> [Int]
    digits = map (read . pure)
  
    -- based on code from
    -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#val
    val :: Integer -> [Int] -> Integer
    val base = foldl' go 0
      where go r d = r * base + fromIntegral d
       
    -- based on code from
    -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#fracExp
    frac :: Integer -> Integer -> [Int] -> Rational
    frac exp mant fs = if exp' < 0
      then mant' % (10 ^ (-exp'))
      else  fromInteger (mant' * 10^exp')
      where
        (exp', mant') = foldl' go (exp, mant) fs
        go (e, r) d = (e-1, r * 10 + fromIntegral d)

parseInteger
 :: Num r => (String -> Integer) -> INTEGER -> r
parseInteger digit2dig a =
  fromInteger (digit2dig (integerToList a))

parseExponential
 :: (String -> Integer) -> EXPONENTIAL -> Integer
parseExponential digit2dig (EXPONENTIAL_ECHAR a b) =
  case a of
    Just SIGN_NEGATIVE -> -(parseInteger digit2dig b)
    _                  -> parseInteger digit2dig b

integerToList :: INTEGER -> [Char]
integerToList (INTEGER_CHAR a INTEGER_END) = [a]
integerToList (INTEGER_CHAR a (INTEGER_UNDERSCORESEP b)) =
  a : integerToList b
integerToList (INTEGER_CHAR a (INTEGER b)) =
  a : integerToList b

-- To show

showNumLiteral :: NUMLITERAL -> ShowS
showNumLiteral (LITERAL_PREFIXBIN a) =
  showString "0b" .
  showInteger a
showNumLiteral (LITERAL_PREFIXOCT a) =
  showString "0o" .
  showInteger a
showNumLiteral (LITERAL_PREFIXDEC a) = 
  showString "0d" .
  showInteger a
showNumLiteral (LITERAL_PREFIXHEX a) =
  showString "0x" .
  showInteger a
showNumLiteral (LITERAL_INTEGER a b c) =
  maybe id showSign a .
  showInteger b .
  maybe id showFractional c
showNumLiteral (LITERAL_PERIOD a b) =
  showChar '.' .
  showInteger a .
  maybe id showExponential b

showInteger :: INTEGER -> ShowS
showInteger (INTEGER_CHAR a INTEGER_END) =
  showChar a
showInteger (INTEGER_CHAR a (INTEGER_UNDERSCORESEP b)) =
  showChar a .
  showChar '_' .
  showInteger b
showInteger (INTEGER_CHAR a (INTEGER b)) =
  showChar a .
  showInteger b

showSign :: SIGN -> ShowS
showSign SIGN_POSITIVE = showChar '+'
showSign SIGN_NEGATIVE = showChar '-'

showFractional :: FRACTIONAL -> ShowS
showFractional (FRACTIONAL_PERIOD a) =
  showChar '.' .
  showFractionalPeriod a
  where
    showFractionalPeriod :: FRACTIONAL_PERIOD -> ShowS
    showFractionalPeriod FRACTIONAL_END = id
    showFractionalPeriod (FRACTIONAL_INTEGER a b) =
      showInteger a .
      maybe id showExponential b
showFractional (FRACTIONAL_EXPONENTIAL a) = showExponential a

showExponential :: EXPONENTIAL -> ShowS
showExponential (EXPONENTIAL_ECHAR a b) =
  showChar 'e' . maybe id showSign a . showInteger b

-- Syntax class instances

instance Num NUMLITERAL where
  fromInteger i =
    LITERAL_INTEGER Nothing (digitsToInteger (show i)) Nothing
  (+) = error "Num NUMLITERAL: (+)"
  (*) = error "Num NUMLITERAL: (*)"
  abs = error "Num NUMLITERAL: abs"
  negate = error "Num NUMLITERAL: negate"
  signum = error "Num NUMLITERAL: signum"

digitsToInteger :: String -> INTEGER
digitsToInteger [] = error "digitsToInteger: []"
digitsToInteger (c:cs) = INTEGER_CHAR c b where
  b = foldr (INTEGER ... INTEGER_CHAR) INTEGER_END cs

instance Fractional NUMLITERAL where
  fromRational = rationalToNumLiteral
  (/) = error "Fractional NUMLITERAL: (/)"

rationalToNumLiteral :: Rational -> NUMLITERAL
rationalToNumLiteral r =
  LITERAL_INTEGER sign (digitsToInteger b) (Just frac)
  where
    frac =
      FRACTIONAL_PERIOD (FRACTIONAL_INTEGER (digitsToInteger c) d)
    (sign, pos) = case fromRational r of
       s -> if s < 0 then
        (Just SIGN_NEGATIVE, -s) else
        (Nothing, s)
    (ns, e) = toDecimalDigits pos
    ds = map intToDigit ns
    (b, c, d) = if e < 0 || e > 7 then
      partsExponent ds e else
      partsFixed ds e
    
    partsExponent (d:ds) e = ([d], ds, Just exp) where
      exp = EXPONENTIAL_ECHAR sign (digitsToInteger (show e'))
      (sign, e') = if e < 0 then 
        (Just SIGN_NEGATIVE, -e) else
        (Nothing, e)
    partsExponent [] e =
      error "rationalToNumLiteral/partsExponent: []"
    
    -- based on code from
    --https://hackage.haskell.org/package/scientific-0.3.6.2/docs/src/Data.Scientific.html#fmtAsFixed
    partsFixed ds e
      | e <= 0 = ("0", replicate (-e) '0' ++ ds, Nothing)
      | otherwise = f e "" ds where
          f 0 s rs     = (mk0 (reverse s), mk0 rs, Nothing)
          f n s ""     = f (n-1) ('0':s) ""
          f n s (r:rs) = f (n-1) (r:s)   rs
          mk0 "" = "0"
          mk0 ls = ls

{-
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
-}
    
-- We can concretely represent *TEXTLITERAL*
-- by wrapping the regular Haskell string.

newtype TEXTLITERAL = TEXTLITERAL_QUOTE String

-- Parse 

tokTextLiteral :: TokenParser TEXTLITERAL
tokTextLiteral = textFragment <?> "text literal"
  where 
    textFragment =
      Parsec.between
        (Parsec.char '"')
        (Parsec.char '"')
        (TEXTLITERAL_QUOTE <$> Parsec.many notQuote)
  
notQuote :: TokenParser Char
notQuote = Parsec.noneOf "\"\\" <|> escapedChars

escapedChars :: TokenParser Char
escapedChars = do
  Parsec.char '\\'
  x <- Parsec.oneOf "\\\"nrt"
  return
    (case x of
      '\\' -> x
      '"' -> x
      'n' -> '\n'
      'r' -> '\r'
      't' -> '\t')

-- To syntax 

parseTextLiteral :: TextLiteral_ r => TEXTLITERAL -> r
parseTextLiteral (TEXTLITERAL_QUOTE a) = quote_ a

-- To show

showTextLiteral :: TEXTLITERAL -> ShowS
showTextLiteral (TEXTLITERAL_QUOTE a) =
  showChar '"' .
  showLitString a .
  showChar '"'

showLitString :: String -> ShowS
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)

-- Syntax class instance

instance TextLiteral_ TEXTLITERAL where
  quote_ s = TEXTLITERAL_QUOTE s

{-
Keyword
-------

A *KEYWORD* is an at-sign '@' followed by an *IDENTIFIER*.

    KEYWORD := '@' IDENTIFIER
-}

-- Concretely

newtype KEYWORD = KEYWORD_ATSIGN IDENTIFIER
getKeyword (KEYWORD_ATSIGN a) = getIdentifier a

-- Parse

tokKeyword :: TokenParser KEYWORD
tokKeyword = (do
  Parsec.char '@'
  b <- tokIdentifer
  return (KEYWORD_ATSIGN b)) <?>
  "keyword"

-- Show

showKeyword :: String -> ShowS
showKeyword b =
  showChar '@' . showIdentifier (IDENTIFIER b)
