module Myc.Parser
  ( float
  , decimal
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , ident
  , name
  , local_route
  , route
  , lhs
  , rhs
  , expr
  , node
  , app
  , program
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
  
-- | My-language
newtype MyNumber = MyNumber Double
newtype MyIdent = MyIdent String
data MyName = Ident MyIdent | Key MyRval
newtype MyLocalRoute = MyLocalRoute [MyName]
data MyRoute = Absolute MyIdent MyLocalRoute | Local MyLocalRoute
data MyLval = Lroute MyRoute | Unnode MyUnnode
data MyUnexpr = Unassign MyLocalRoute MyLval | Pack MyLval
newtype MyUnnode = MyUnnode [MyUnexpr]
data MyRval = Number MyNumber | String String | Rroute MyRoute | Node MyNode | App MyApp
data MyExpr = Assign MyLval MyRval | Eval MyRval | Unpack MyRval
newtype MyNode = MyNode [MyExpr]
newtype MyApp = MyApp MyRval MyRval

  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer d =
  do{ x <- d
    ; xs <- many $ (optional (char '_') >> d)
    ; return (x:xs)
    }

-- | Parser for valid floating point number
float :: Parser MyNumber
float =
  do{ xs <- integer digit
    ; y <- char '.'
    ; ys <- option "0" (integer digit)
    ; return MyNumber $ read $ (xs ++ [y] ++ ys)
    }

-- | Parser for valid decimal number
decimal :: Parser MyNumber
decimal = optional (try $ string "0d") >> integer digit >>= return . MyNumber . read

-- | Parser for valid binary number
binary :: Parser MyNumber
binary = (try $ string "0d") >> integer (oneOf "01") >>= return . MyNumber . bin2dig
  where bin2dig = foldr (\x digint -> 2 * digint + (if x=='0' then 0 else 1)) 0

-- | Parser for valid octal number
octal :: Parser MyNumber
octal = (try $ string "0o") >> integer octDigit >>= return . MyNumber . oct2dig
  where oct2dig = fst $ readOct x !! 0

-- | Parser for valid hexidecimal number
hexidecimal :: Parser MyNumber
hexidecimal = (try $ string "0x") >> integer hexDigit >>= return . MyNumber . hex2dig
  where hex2dig = fst $ readHex x !! 0
                 
-- | Parser for valid numeric value
number :: Parser MyRval
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
string :: Parser MyRval
string = between (char '"') (char '"') (many $ escapedChars <|> noneOf "\"\\") >>= return . String . MyString


-- | Parser that succeeds when consuming a valid identifier string.
ident :: Parser MyIdent
ident =
  do{ x <- letter
    ; xs <- many alphaNum
    ; return MyIdent (x:xs)
    }

-- | Parse a valid node name
name :: Parser MyName
name =  ident >>= return . Ident
    <|> between (char '(' >> spaces) (spaces >> char ')') rhs >>= return . Key


-- | Parser that succeeds when consuming a non-newline space character
nonbreak = notFollowedBy newline >> space

-- | Parse an expression break
break = many nonbreak >> (char ';' <|> newline) >> spaces


-- | Parse a local route
local_route :: Parser MyLocalRoute
local_route = many1 (char '.' >> name) >>= return . MyLocalRoute

-- | My-language route

-- | Parse a route
route :: Parser MyRoute
route = local_route >>= return . Local
     <|> do{ x <- ident
           ; y <- local_route
           ; return $ Absolute x y
           }

lhs :: Parser MyLval
lhs =  route >>= return . Lroute
   <|> unnode >>= return . Unnode

assign_unexpr :: Parser MyUnexpr
assign_unexpr = 
  do{ x <- local_route
    ; spaces
    ; char '='
    ; spaces
    ; y <- lhs
    ; return $ Unassign x y
    }

pack_unexpr :: Parser MyUnexpr
pack_unexpr = string "..." >> route >>= return . Lroute


-- | Parse a destructuring expression
unnode :: Parser MyUnnode
unnode =
  do{ char '{'
    ; spaces
    ; x <- unexpr
    ; xs <- many (break >> unexpr)
    ; ys <- option [] pack_expr
    ; zs <- option [] (many (break >> unexpr))
    ; return MyUnnode (xs ++ ys ++ zs)
    }
            
-- | Parse an rvalue
rhs :: Parser MyRval
rhs =  string
   <|> number
   <|> route >>= return . Rroute
   <|> node >>= return . Node

-- | Parse an assignment expression
assign_expr :: Parser MyExpr
assign_expr =
  do{ x <- lhs
    ; spaces
    ; char "="
    ; spaces
    ; y <- rhs
    ; return Assign x y
    }

--- | Parse an eval expression
eval_expr :: Parser MyExpr
eval_expr = rhs >>= return . Eval

-- | Parse an unpack expression
unpack_expr :: Parser MyExpr
unpack_expr = string "..." >> (   node >>= return . Unpack . Node
                             <|> route >>= return . Unpack . Rroute
                              )

-- | Parse any expression
expr = assign_expr <|> eval_expr <|> unpack_expr

-- | Parse a curly-brace wrapped sequence of expressions
node :: Parser MyNode
node =
  do{ char '{'
    ; spaces
    ; x <- expr
    ; xs <- many (break >> expr)
    ; spaces
    ; return MyNode (x:xs)
    }

-- | Parse an application
application :: Parser MyApp
application =
  do{ x <- rhs
    ; y <- between (char '(' >> spaces) (spaces >> char ')') rhs
    ; return MyApp x y
    }

-- | Parse a top-level sequence of expressions
program ;: Parser MyNode
program =
  do{ spaces
    ; x <- expr
    ; xs <- many (break >> expr)
    ; spaces
    ; return MyNode (x:xs)
    }


