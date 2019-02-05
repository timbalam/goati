module Goat.Syntax.Extern
  where
  
import Goat.Co
import Goat.Syntax.Keyword (parseKeyword, showKeyword)
import Goat.Syntax.Ident (Ident, parseIdent, showIdent)
import Data.String (fromString)
import Data.Void (absurd)
import Text.Parsec.Text (Parser)


-- | Use an external name
class Extern_ r where
  use_ :: String -> r

parseExtern :: Extern_ r => Parser r
parseExtern = do
  parseKeyword "use"
  i <- parseIdent
  return (use_ i)

newtype Extern a = Use String
  deriving (Eq, Ord, Show)

instance Extern_ (Comp (Extern <: k) a) where
  use_ s = send (Use s)

showExtern :: Comp (Extern <: k) ShowS -> Comp k ShowS
showExtern (Done s) = Done s
showExtern (Req (Head (Use s)) _) =
  Done (showKeyword "use" . showChar ' ' . showIdent s)
showExtern (Req (Tail r) k) = Req (Tail r) (showExtern . k)

fromExtern :: Extern_ r => Comp (Extern <: k) r -> Comp k r
fromExtern = handle fromExtern'
  where fromExtern' (Use i) = use_ i