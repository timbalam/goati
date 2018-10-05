-- | My language exception machinery
module My.Types.Error
  ( module My.Types.Error
  ) where
  
import qualified My.Types.Syntax as P
import My.Types.Syntax.Class (Ident)
import My.Syntax.Parser (showIdent)
import Data.Bifunctor (first)
import Data.Foldable (foldr)
import Data.List (intersperse)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Data.Monoid (Endo(..))
import Data.Typeable
import qualified Data.Text as T
import qualified Text.Parsec
--import Control.Exception
--import Control.Monad.Catch (MonadThrow(..))


displayErrorList :: (e -> String) -> [e] -> String
displayErrorList displayError es = (foldMap id
  . intersperse "\n") (fmap displayError es)

-- | Dynamic exception
data DynError k =
    StaticError (StaticError k)
  | TypeError (TypeError k)
  deriving (Eq, Show)
  
  
displayDynError :: DynError Ident -> String
displayDynError (StaticError e) = displayStaticError e
displayDynError (TypeError e)   = displayTypeError e
displayDynError _               = "unknown error"


data StaticError k =
    DefnError (DefnError k)
  | ScopeError ScopeError
  | ParseError Text.Parsec.ParseError
  deriving (Eq, Show)
  
displayStaticError :: StaticError Ident -> String
displayStaticError (DefnError e)  = displayDefnError e
displayStaticError (ScopeError e) = displayScopeError e
displayStaticError (ParseError e) = show e


eitherError
  :: (StaticError k -> Maybe e) 
  -> ([StaticError k], a)
  -> Either [e] a
eitherError f p = case first (mapMaybe f) p of
  ([], a) -> Right a
  (es, _) -> Left es
  
maybeDefnError (DefnError de) = Just de
maybeDefnError _              = Nothing
  


-- | Errors from binding definitions
data DefnError k =
    OlappedMatch k
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet (P.Vis Ident k)
  -- ^ Error if a group assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately in a group
  deriving (Eq, Show)
  
  
displayDefnError :: DefnError Ident -> String
displayDefnError (OlappedMatch p) =
  "error: Multiple component matches: " ++ showIdent p ""
displayDefnError (OlappedSet p) =
  "error: Multiple assignments: " ++ P.vis showIdent showIdent p ""
displayDefnError (OlappedVis i) =
  "error: Multiple visibilities: " ++ showIdent i ""
  
  
newtype ScopeError = NotDefined Ident
  deriving (Eq, Show)
  
displayScopeError :: ScopeError -> String
displayScopeError (NotDefined i) =
  "error: Missing assignment: " ++ showIdent i ""

  
data TypeError k =
    NotComponent k
  | NotNumber
  | NotText
  | NotBool
  | NoPrimitiveSelf
  | NoGlobalSelf
  deriving (Eq, Show)
  
displayTypeError :: TypeError Ident -> String
displayTypeError (NotComponent i) =
  "error: Missing component: " ++ showIdent i ""
displayTypeError NotNumber =
  "error: Number expected"
displayTypeError NotText =
  "error: Text expected"
displayTypeError NotBool =
  "error: Bool expected"
displayTypeError NoPrimitiveSelf =
  "error: Accessed primitive component"
displayTypeError NoGlobalSelf =
  "error: Accessed global component "
