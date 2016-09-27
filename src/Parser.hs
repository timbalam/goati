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
import qualified Types as T
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  do{ x <- d
    ; xs <- P.many $ (P.optional (P.char '_') >> d)
    ; return (x:xs)
    }
    
-- | Parser for valid floating point number
float :: Parser T.Rval
float =
  do{ xs <- integer P.digit
    ; y <- P.char '.'
    ; ys <- P.option "0" (integer P.digit)
    ; return $ T.Number $ read $ (xs ++ [y] ++ ys)
    }

-- | Parser for valid decimal number
decimal :: Parser T.Rval
decimal = P.optional (P.try $ P.string "0d") >> integer P.digit >>= return . T.Number . read

-- | Parser for valid binary number
binary :: Parser T.Rval
binary = (P.try $ P.string "0d") >> integer (P.oneOf "01") >>= return . T.Number . bin2dig
  where bin2dig = foldr (\x digint -> 2 * digint + (if x=='0' then 0 else 1)) 0

-- | Parser for valid octal number
octal :: Parser T.Rval
octal = (P.try $ P.string "0o") >> integer P.octDigit >>= return . T.Number . oct2dig
  where oct2dig x = fst $ readOct x !! 0

-- | Parser for valid hexidecimal number
hexidecimal :: Parser T.Rval
hexidecimal = (P.try $ P.string "0x") >> integer P.hexDigit >>= return . T.Number . hex2dig
  where hex2dig x = fst $ readHex x !! 0
                 
-- | Parser for valid numeric value
number :: Parser T.Rval
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
string :: Parser T.Rval
string = P.between (P.char '"') (P.char '"') (P.many $ escapedChars <|> P.noneOf "\"\\") >>= return . T.String

-- | Parser that succeeds when consuming a valid identifier string.
ident :: Parser T.Ident
ident =
  do{ x <- P.letter
    ; xs <- P.many P.alphaNum
    ; return $ T.Ident (x:xs)
    }
    
-- | Parser that parses whitespace
spaces = P.spaces

-- | Parse a valid node name
name :: Parser T.Name
name =  (ident >>= return . T.Ref)
    <|> (P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs >>= return . T.Key)

-- | Parse an expression break
expr_break = P.between spaces spaces (P.char ';') >> return ()


-- | Parse a local route
local_route :: Parser T.LocalRoute
local_route = P.many (P.char '.' >> spaces >> name) >>= return . T.LocalRoute

-- | Parse a route
route :: Parser T.Route
route = (local_route >>= return . T.Local)
     <|> do{ x <- ident
           ; y <- local_route
           ; return $ T.Absolute x y
           }

lhs :: Parser T.Lval
lhs =  (route >>= return . T.Lroute)
   <|> unnode

assign_unexpr :: Parser T.Unexpr
assign_unexpr = 
  do{ x <- local_route
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- lhs
    ; return $ T.Unassign x y
    }

pack_unexpr :: Parser T.Unexpr
pack_unexpr = P.string "..." >> route >>= return . T.Pack . T.Lroute

-- | Parse a destructuring expression
unnode :: Parser T.Lval
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
        ; return $ T.Unnode (xs ++ ys)
        }
            
-- | Parse an rvalue
rhs :: Parser T.Rval
rhs =  string
   <|> number
   <|> (route >>= return . T.Rroute)
   <|> node

-- | Parse an assignment expression
assign_expr :: Parser T.Expr
assign_expr =
  do{ x <- lhs
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- rhs
    ; return $ T.Assign x y
    }

--- | Parse an eval expression
eval_expr :: Parser T.Expr
eval_expr = rhs >>= return . T.Eval

-- | Parse an unpack expression
unpack_expr :: Parser T.Expr
unpack_expr =
  P.string "..."
    >> ( node <|> (route >>= return . T.Rroute) )
    >>= return . T.Unpack

-- | Parse any expression
expr = assign_expr <|> eval_expr <|> unpack_expr

-- | Parse a curly-brace wrapped sequence of expressions
node_body :: Parser T.Rval
node_body =
  do{ 
    ; x <- expr
    ; xs <- P.many (expr_break >> expr)
    ; return $ T.Node (x:xs)
    }
    
node :: Parser T.Rval
node = P.between (P.char '{' >> spaces) (spaces >> P.char '}') node_body

-- | Parse an application
application :: Parser T.Rval
application =
  do{ x <- rhs
    ; y <- P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs
    ; return $ T.App x y
    }

-- | Parse a top-level sequence of expressions
program :: Parser T.Rval
program = P.between spaces spaces node_body


