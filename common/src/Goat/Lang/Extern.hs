{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Goat.Lang.Extern
  where
  
import Goat.Comp
import Goat.Lang.Keyword
import Goat.Lang.Ident
import Goat.Lang.Comment (spaces)
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

showExtern :: Extern a -> ShowS
showExtern (Use s) =
  showKeyword "use" . showChar ' ' . ident showString s

fromExtern :: Extern_ r => Extern a -> r
fromExtern (Use i) = use_ i

instance Extern_ (Extern r) where use_ = Use

instance Member Extern r => Extern_ (Comp r a) where
  use_ i = send (Use i)
