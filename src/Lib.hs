module Lib
  ( someFunc
  ) where
import Text.Parsec.String
  ( Parser
  )
import Text.Parsec
  ( letter
  , alphaNum
  , digit
  , hexDigit
  , octDigit
  , char
  , string
  , space
  , spaces
  , newline
  , many
  , many1
  , between
  , oneOf
  , noneOf
  , notFollowedBy
  )
import Numeric
  ( readHex
  , readOct
  )
  
-- | Parser that succeeds when consuming a string of underscore spaced digits
integer d =
  do{ x <- d
    ; xs <- many $ (optional (char '_') >> d)
    ; return (x:xs)
    }

-- | My-language numeric type
data MyNumber = MyI Integer
              | MyF Double

-- | Parser for valid floating point number
float :: Parser MyNumber
float =
  do{ xs <- integer digit
    ; y <- char '.'
    ; ys <- option "0" (integer digit)
    ; return MyF $ read $ (xs ++ [y] ++ ys)
    }

-- | Parser for valid decimal number
decimal :: Parser MyNumber
decimal = optional (try $ string "0d") >> integer digit >>= return . MyI . read

-- | Parser for valid binary number
binary :: Parser MyNumber
binary = (try $ string "0d") >> integer (oneOf "01") >>= return . MyI . bin2dig
  where bin2dig = foldr (\x digint -> 2 * digint + (if x=='0' then 0 else 1)) 0

-- | Parser for valid octal number
octal :: Parser MyNumber
octal = (try $ string "0o") >> integer octDigit >>= return . MyI . oct2dig
  where oct2dig = fst $ readOct x !! 0

-- | Parser for valid hexidecimal number
hexidecimal :: Parser MyNumber
hexidecimal = (try $ string "0x") >> integer hexDigit >>= return . MyI . hex2dig
  where hex2dig = fst $ readHex x !! 0

-- | My-language primitives
data MyPrimitive = String String
                 | Number MyNumber
                 
-- | Parser for valid numeric value
number :: Parser MyPrimitive
number = (binary <|> octal <|> hexidecimal <|> float <|> decimal) >>= return . Number

-- | Parser that succeeds when consuming an escaped character.
escapedChars =
  do{ char '\\'
    ; x <- oneOf "\\\"nrt"
    ; return $ case x of{ '\\' -> x
                        ; '"'  -> x
                        ; 'n'  -> '\n'
                        ; 'r'  -> '\r'
                        ; 't'  -> '\t'
                        }

-- | Parser that succeeds when consuming a double-quote wrapped string.
string :: Parser MyPrimitive
string = between (char '"') (char '"') (many $ escapedChars <|> noneOf "\"\\") >>= return . String

-- | My-language identifier
data MyIdent = MyIdent String

-- | Parser that succeeds when consuming a valid identifier string.
ident :: Parser MyIdent
ident =
  do{ x <- letter
    ; xs <- many alphaNum
    ; return MyIdent (x:xs)
    }

-- | Parser that succeeds when consuming a non-newline space character
nonbreak = notFollowedBy newline >> space

-- | Parse an expression break
break = many nonbreak >> (char ';' <|> newline) >> spaces

-- | My-language name
data MyName = Ident MyIdent
            | Key MyRVal

-- | Parse a valid node name
name :: Parser MyName
name =  ident >>= return . Ident
    <|> between (char '(' >> spaces) (spaces >> char ')') rhs >>= return . Key

-- | My-language route
data MyRoute = Route Ident [MyName]
             | LocalRoute [MyName]

-- | Parse a local route
local_route :: Parser MyRoute
local_route = many1 (char '.' >> name) >>= return . LocalRoute

-- | Parse a route
route :: Parser MyRoute
route = local_route
     <|> do{ x <- name
           , LocalRoute y <- local_route
           , return $ Route x y
           }

-- | Parser that succeeds when consuming a node declaration
node :: Parser MyVal
node =
  do{ char '{'
    ; optional (char '.')
    ; try $
      do
        x <- lhs
        char '='
        return x
    }
    
-- | Parser that succeeds when consuming a valid lvalue
lhs :: Parser MyVal
lhs = ident
   <|> between (char '(') (string <|> number)

-- | Parser that succeeds when consuming a valid rvalue
rhs :: Parser MyVal
rhs = lhs
  <|> string
  <|> number
  <|> node


-- | Parser that succeeds when consuming a bracket-wrapped identifier or literal object
index :: Parser String
index =
  do{ char '('
    ; x <- ident <|> 
    
-- | Parser that succeeds when consuming a valid member string.
member :: Parser String
member = char '.' >> ident



-- | My-language 
--
data MyPrimitive = Ident String
           | String String
           | Number MyNumeric
           | Node MyVal


