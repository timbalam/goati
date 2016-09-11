module Parser
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
  , application
  , program
  ) where
import qualified Text.Parsec as P
import Text.Parsec
  ( (<|>)
  , (<?>)
  )
import Text.Parsec.String
  ( Parser
  )
import Numeric
  ( readHex
  , readOct
  ) 

-- | My language rval
data MyRval = Number Double | String String | Rroute MyRoute | Node MyNode | App MyApp
data MyExpr = Assign MyLval MyRval | Eval MyRval | Unpack MyRval
newtype MyNode = MyNode [MyExpr]
data MyApp = MyApp MyRval MyRval
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  do{ x <- d
    ; xs <- P.many $ (P.optional (P.char '_') >> d)
    ; return (x:xs)
    }
    
-- | Parser for valid floating point number
float :: Parser MyRval
float =
  do{ xs <- integer P.digit
    ; y <- P.char '.'
    ; ys <- P.option "0" (integer P.digit)
    ; return $ Number $ read $ (xs ++ [y] ++ ys)
    }

-- | Parser for valid decimal number
decimal :: Parser MyRval
decimal = P.optional (P.try $ P.string "0d") >> integer P.digit >>= return . Number . read

-- | Parser for valid binary number
binary :: Parser MyRval
binary = (P.try $ P.string "0d") >> integer (P.oneOf "01") >>= return . Number . bin2dig
  where bin2dig = foldr (\x digint -> 2 * digint + (if x=='0' then 0 else 1)) 0

-- | Parser for valid octal number
octal :: Parser MyRval
octal = (P.try $ P.string "0o") >> integer P.octDigit >>= return . Number . oct2dig
  where oct2dig x = fst $ readOct x !! 0

-- | Parser for valid hexidecimal number
hexidecimal :: Parser MyRval
hexidecimal = (P.try $ P.string "0x") >> integer P.hexDigit >>= return . Number . hex2dig
  where hex2dig x = fst $ readHex x !! 0
                 
-- | Parser for valid numeric value
number :: Parser MyRval
number = (binary <|> octal <|> hexidecimal <|> float <|> decimal)

-- | Parser that succeeds when consuming an escaped character.
escapedChars =
  do{ P.char '\\'
    ; x <- P.oneOf "\\\"nrt"
    ; return $
      case
        x
      of
      { '\\' -> x
      ; '"'  -> x
      ; 'n'  -> '\n'
      ; 'r'  -> '\r'
      ; 't'  -> '\t'
      }
    }

-- | Parser that succeeds when consuming a double-quote wrapped string.
string :: Parser MyRval
string = P.between (P.char '"') (P.char '"') (P.many $ escapedChars <|> P.noneOf "\"\\") >>= return . String

-- | My-language identifiers
newtype MyIdent = MyIdent String
data MyName = Ident MyIdent | Key MyRval
newtype MyLocalRoute = MyLocalRoute [MyName]
data MyRoute = Absolute MyIdent MyLocalRoute | Local MyLocalRoute

-- | Parser that succeeds when consuming a valid identifier string.
ident :: Parser MyIdent
ident =
  do{ x <- P.letter
    ; xs <- P.many P.alphaNum
    ; return $ MyIdent (x:xs)
    }
    
-- | Parser that parses whitespace
spaces = P.spaces

-- | Parse a valid node name
name :: Parser MyName
name =  (ident >>= return . Ident)
    <|> (P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs >>= return . Key)


-- | Parser that succeeds when consuming a non-newline space character
nonbreak = P.notFollowedBy P.newline >> P.space

-- | Parse an expression break
expr_break = P.many nonbreak >> (P.char ';' <|> P.newline) >> spaces


-- | Parse a local route
local_route :: Parser MyLocalRoute
local_route = P.many1 (P.char '.' >> name) >>= return . MyLocalRoute

-- | Parse a route
route :: Parser MyRoute
route = (local_route >>= return . Local)
     <|> do{ x <- ident
           ; y <- local_route
           ; return $ Absolute x y
           }
           
-- | My-language lval
data MyLval = Lroute MyRoute | Unnode MyUnnode
data MyUnexpr = Unassign MyLocalRoute MyLval | Pack MyLval
newtype MyUnnode = MyUnnode [MyUnexpr]

lhs :: Parser MyLval
lhs =  (route >>= return . Lroute)
   <|> (unnode >>= return . Unnode)

assign_unexpr :: Parser MyUnexpr
assign_unexpr = 
  do{ x <- local_route
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- lhs
    ; return $ Unassign x y
    }

pack_unexpr :: Parser MyUnexpr
pack_unexpr = P.string "..." >> route >>= return . Pack . Lroute

-- | Parse a destructuring expression
unnode :: Parser MyUnnode
unnode = P.between (P.char '{' >> spaces) (spaces >> P.char '{') unnode_body
  where
    unnode_pack_list =
      do{ x <- pack_unexpr
        ; return [x]
        }
    unnode_assign_first =
      do{ x <- assign_unexpr
        ; xs <- P.many (expr_break >> assign_unexpr)
        ; ys <- P.option [] (expr_break >> unnode_pack_list)
        ; return $ (x:xs) ++ ys
        }
    unnode_body =
      do{ xs <- unnode_assign_first <|> unnode_pack_list
        ; ys <- P.option [] (P.many (expr_break >> assign_unexpr))
        ; return $ MyUnnode (xs ++ ys)
        }
            
-- | Parse an rvalue
rhs :: Parser MyRval
rhs =  string
   <|> number
   <|> (route >>= return . Rroute)
   <|> (node >>= return . Node)

-- | Parse an assignment expression
assign_expr :: Parser MyExpr
assign_expr =
  do{ x <- lhs
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- rhs
    ; return $ Assign x y
    }

--- | Parse an eval expression
eval_expr :: Parser MyExpr
eval_expr = rhs >>= return . Eval

-- | Parse an unpack expression
unpack_expr :: Parser MyExpr
unpack_expr = P.string "..." >> (  (node >>= return . Unpack . Node)
                               <|> (route >>= return . Unpack . Rroute)
                                )

-- | Parse any expression
expr = assign_expr <|> eval_expr <|> unpack_expr

-- | Parse a curly-brace wrapped sequence of expressions
node_body :: Parser MyNode
node_body =
  do{ 
    ; x <- expr
    ; xs <- P.many (expr_break >> expr)
    ; return $ MyNode (x:xs)
    }
    
node :: Parser MyNode
node = P.between (P.char '{' >> spaces) (spaces >> P.char '}') node_body

-- | Parse an application
application :: Parser MyApp
application =
  do{ x <- rhs
    ; y <- P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs
    ; return $ MyApp x y
    }

-- | Parse a top-level sequence of expressions
program :: Parser MyNode
program = P.between spaces spaces node_body


