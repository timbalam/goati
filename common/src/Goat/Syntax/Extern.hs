{-# LANGUAGE TypeOperators, FlexibleInstances, FlexibleContexts #-}
module Goat.Syntax.Extern
  where
  
import Goat.Co
import Goat.Syntax.Keyword
import Goat.Syntax.Ident
import Goat.Syntax.Comment (spaces)
import Data.String (fromString)
import Data.Void (absurd)
import Text.Parsec.Text (Parser)


-- | Use an external name
class Extern_ r where
  use_ :: Ident -> r

parseExtern :: Extern_ r => Parser r
parseExtern = do
  parseKeyword "use"
  i <- parseIdent
  spaces
  return (use_ i)

newtype Extern a = Use Ident deriving (Eq, Ord, Show)

instance Member Extern r => Extern_ (Comp r a) where
  use_ i = send (Use i)

showExtern
 :: Comp (Extern <: t) ShowS -> Comp t ShowS
showExtern  = handle (\ (Use s) _ -> return (showUse' s))
  where
    showUse' s =
      showKeyword "use"
        . showChar ' '
        . ident showString s

fromExtern
 :: Extern_ r
 => Comp (Extern <: t) r -> Comp t r
fromExtern = handle (\ (Use i) _ -> return (use_ i))
