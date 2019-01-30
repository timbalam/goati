module Goat.Syntax.Number
  where

import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Symbol (parseSymbol, Symbol(..))
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import Text.Read (readMaybe)
import Numeric (readHex, readOct)
import Data.Ratio ((%))
import Data.Foldable (foldl')


newtype Number = Number Double
  deriving (Eq, Show)
  
nume = error "Num Number"
  
instance Num Number where
  fromInteger = Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  
instance Fractional Number where
  fromRational = Number . fromRational
  (/) = nume
  
-- | Parse any valid numeric literal
parseNumber :: Fractional r => Parser r
parseNumber =
  (parseBinary
    <|> parseOctal
    <|> parseHexidecimal
    <|> parseDecfloat
    <?> "number literal")
    <* spaces
    
showNumber :: Number -> ShowS
showNumber (Number d) = shows d

fromNumber :: Fractional r => Number -> r
fromNumber (Number d) = fromRational (toRational d)


-- | Parse a valid binary number
parseBinary :: Num r => Parser r
parseBinary =
  tryPrefixedDigitString "0b" bin2dig (Parsec.oneOf "01")
  where
    bin2dig =
      foldl'
        (\digint x -> 2 * digint + (if x=='0' then 0 else 1))
        0

        
-- | Parse a valid octal number
parseOctal :: Num r => Parser r
parseOctal =
  tryPrefixedDigitString "0o" oct2dig Parsec.octDigit
  where
    oct2dig x =
      fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
parseHexidecimal :: Num r => Parser r
parseHexidecimal =
  tryPrefixedDigitString "0x" hex2dig Parsec.hexDigit
  where 
    hex2dig x =
      fst (readHex x !! 0)

  
-- | Parser for valid decimal or floating point number
parseDecfloat :: (Num r, Fractional r) => Parser r
parseDecfloat =
  prefixed
    <|> unprefixed
  where
    prefixed =
      tryPrefixedDigitString "0d" (val 10) digit
        
    unprefixed =
      do
        Parsec.optional (Parsec.char '+')
        ds <- digits
        let i = val 10 ds
        fracnext i                        -- int frac
                                          -- int frac exp
          <|> expnext i []                -- int exp
          <|> return (fromInteger i)      -- int
          
    fracnext i =
      do 
        Parsec.char '.'
        mf <- Parsec.optionMaybe digits
        case mf of
          Nothing ->
            return (fromRational (fromInteger i))     -- frac
            
          Just f ->
            expnext i f                               -- frac exp
              <|> return (fromRational (frac 0 i f))  -- frac
          
    expnext i f =
      do 
        Parsec.oneOf "eE"
        sgn <- (do 
          s <- Parsec.oneOf "+-"
          return [s])
          <|> return []
        ds <- digits
        let
          exp =
            if sgn == "-"
              then -(val 0 ds)
              else val 0 ds
        return (fromRational (frac exp i f))
        
    -- based on code from
    -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#val
    val :: Integer -> [Int] -> Integer
    val base = foldl' go 0
      where
        go r d = r * base + fromIntegral d
        
    -- based on code from
    -- http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Text.Read.Lex.html#fracExp
    frac :: Integer -> Integer -> [Int] -> Rational
    frac exp mant fs = if exp' < 0
      then mant' % (10 ^ (-exp'))
      else  fromInteger (mant' * 10^exp')
      where
        (exp', mant') = foldl' go (exp, mant) fs
        go (e, r) d = (e-1, r * 10 + fromIntegral d)


-- | Parse a digit
digit :: Parser Int
digit = do
  d <- Parsec.digit
  return (read [d])
  

-- | Parse a list of digits
digits :: Parser [Int]
digits = digitString digit
        
      
tryPrefixedDigitString
  :: Num r
  => String
  -> ([a] -> Integer)
  -> Parser a
  -> Parser r
tryPrefixedDigitString prefix digit2dig digit =
  do
    Parsec.try (Parsec.string prefix)
    ds <- digitString digit
    return (fromInteger (digit2dig ds))
        
        
-- | Parse a sequence of underscore spaced digits
digitString :: Parser a -> Parser [a]
digitString d =
  (Parsec.sepBy1 d . Parsec.optional) (Parsec.char '_')