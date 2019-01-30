module Goat.Syntax.Extern
  where
  
--import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Goat.Syntax.Keyword (Keyword(..), parseKeyword, showKeyword)
import Goat.Syntax.Ident (Ident, parseIdent, showIdent)
import Data.String (fromString)


-- | Use an external name
newtype Extern = Use Ident deriving (Eq, Ord, Show)

class Extern_ r where
  use_ :: Ident -> r

instance Extern_ Extern where
  use_ = Use
  
parseExtern :: Extern_ r => Parser r
parseExtern = do
  parseKeyword "use"
  i <- parseIdent
  return (use_ i)

showExtern :: Extern -> ShowS
showExtern (Use i) =
  showKeyword "use" . showChar ' ' . showIdent i

fromExtern :: Extern_ r => Extern -> r
fromExtern (Use i) = use_ i