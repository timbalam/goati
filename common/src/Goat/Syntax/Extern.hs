module Goat.Syntax.Extern
  where
  
--import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Goat.Syntax.Keyword (parseKeyword, showKeyword)
import Goat.Syntax.Ident (Ident, parseIdent, showIdent)
import Data.String (fromString)
import Data.Void (absurd)


-- | Use an external name
data Extern a =
    Intern a
  | Use String
  deriving (Eq, Ord, Show)

class Extern_ r where
  use_ :: String -> r

instance Extern_ (Extern a) where
  use_ = Use

showExtern :: (a -> ShowS) -> Extern a -> ShowS
showExtern sa (Intern a) = sa a
showExtern sa (Use s) =
  showKeyword "use" . showChar ' ' . showIdent absurd (fromString s)

fromExtern :: Extern_ r => (a -> r) -> Extern a -> r
fromExtern ka (Intern a) = ka a
fromExtern ka (Use i) = use_ i
  
parseExtern :: Extern_ r => Parser r
parseExtern = do
  parseKeyword "use"
  i <- parseIdent
  return (use_ i)