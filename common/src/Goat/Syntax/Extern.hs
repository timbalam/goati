{-# LANGUAGE TypeOperators, FlexibleInstances #-}
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

instance Extern_ (Comp (Extern <: t) a) where
  use_ s = send (Use s)

showExtern
 :: Comp (Extern <: t) ShowS -> Comp t ShowS
showExtern  = handle (\ (Use s) _ -> return (showUse' s))
  where
    showUse' s =
      showKeyword "use"
        . showChar ' '
        . run (showIdent (fromString s))

fromExtern
 :: Extern_ r
 => Comp (Extern <: t) r -> Comp t r
fromExtern = handle (\ (Use i) _ -> return (use_ i))
