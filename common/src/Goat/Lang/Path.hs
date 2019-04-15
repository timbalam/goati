module Goat.Lang.Path
  where
  
import Goat.Lang.Field
import Goat.Lang.Ident
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Control.Monad (join)
import Data.Bifunctor
import qualified Data.Text as Text
import Data.String (IsString(..))
import Data.Void (Void)
  
-- | Nested field accesses
type Path_ r =
  ( IsString r, Field_ r
  , IsString (Compound r), Chain_ (Compound r)
  )

parsePath
 :: Path_ r => Parser r
parsePath = 
  (do
    s <- parseIdent
    go (fromString s)
      <|> return (fromString s))
    <|> go (fromString "")
  where
    go
      :: (Field_ r, Chain_ (Compound r))
      => Compound r -> Parser r
    go c = do
      f <- parseField
      go (runField (f c))
        <|> return (runField (f c))
    
    runField :: Field_ r => Field (Compound r) -> r
    runField = fromField id

showFieldC
 :: Comp (Field <: t) ShowS -> Comp t ShowS
showFieldC = handle (\ a k -> showField id <$> traverse k a)

fromFieldC
 :: (Field_ r, Compound r ~ r)
 => Comp (Field <: t) r -> Comp t r
fromFieldC = handle (\ a k -> fromField id <$> traverse k a)

--type SomeChain = Comp (Field <: Null) Void

fieldCProof :: Comp (Field <: Null) Void -> Comp (Field <: t) a
fieldCProof = handleAll fromFieldC

{--
type VarChain t = Field <: Var <: t

showVarChainC
 :: Comp (VarChain t) ShowS -> Comp t ShowS
showVarChainC = showVarC . showFieldC

fromVarChainC
 :: (Chain_ r, IsString r) => Comp (VarChain t) r -> Comp t r
fromVarChainC = fromVarC . fromFieldC

type SomeVarChain = Comp (VarChain Null) Void

type SomePath = Union (VarChain Null) SomeVarChain
newtype SomePath =
  SomePath {
    getPath
     :: forall t a
      . Comp (Field SomeVarChain <: Var <: t) a
    }

instance Field_ SomePath where
  type Compound SomePath = SomeVarChain
  c #. i = SomePath (c #. i)

instance IsString SomePath where
  fromString s = SomePath (fromString s)
{--}
showPath
 :: (Union t SomeVarChain -> ShowS)
 -> Union (VarChain t) SomeVarChain -> ShowS
showPath =
  showFieldU (handleAll showVarChainC) . showVarU

fromPath
 :: Path_ r
 => (Union t SomeVarChain -> r)
 -> Union (VarChain t) SomeVarChain -> r
fromPath =
  fromFieldU (handleAll fromVarChainC) . fromVarU

pathProof
 :: SomePath -> Union (VarChain t) (Comp (VarChain t') a)
pathProof = handleAllU fromPath
-}

-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self i = Self | NoSelf i
  deriving (Eq, Show)
  
self :: r -> (i -> r) -> Self i -> r
self ks ki Self = ks
self ks ki (NoSelf i) = ki i

instance IsString i => IsString (Self i) where
  fromString "" = Self
  fromString s = NoSelf (fromString s)
