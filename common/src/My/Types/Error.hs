-- | My language exception machinery
module My.Types.Error
  ( DefnError(..)
  , ScopeError(..)
  , KeyError(..)
  , PrimError(..)
  , MyError(..)
  , displayError
  , displayErrorList
  ) where
  
import qualified My.Types.Syntax as P
import My.Types.Syntax.Class (Ident)
import My.Syntax.Parser (showIdent)
import Data.Foldable (foldr)
import qualified Data.Map as M
import Data.Monoid (Endo(..))
import Data.Typeable
import qualified Data.Text as T
import qualified Text.Parsec
import Control.Exception
import Control.Monad.Catch (MonadThrow(..))

      
-- | Class for displaying exceptions
data MyError k =
    DefnError (DefnError k)
  | ScopeError ScopeError
  | KeyError (KeyError k)
  | ParseError Text.Parsec.ParseError
  | PrimError PrimError
  deriving (Eq, Show)
  
  
displayError :: MyError Ident -> String
displayError (DefnError e)  = displayDefnError e
displayError (ScopeError e) = displayScopeError e
displayError (KeyError e)   = displayKeyError e
displayError (ParseError e) = show e
displayError (PrimError e)  = displayPrimError e
displayError _              = "unknown error"


displayErrorList :: [MyError Ident] -> String
displayErrorList es = appEndo
  (foldMap
    (\ e -> Endo (showString ("\n" ++ displayError e)))
    es)
  ""


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

  
newtype KeyError k = NotComponent k
  deriving (Eq, Show)
  
displayKeyError :: KeyError Ident -> String
displayKeyError (NotComponent i) =
  "error: Missing component: " ++ showIdent i ""

  
data PrimError =
    NoPrimitiveSelf
  | NoGlobalSelf
  deriving (Eq, Show)
  
displayPrimError :: PrimError -> String
displayPrimError NoPrimitiveSelf =
  "error: Accessed Primitive component"
displayPrimError NoGlobalSelf =
  "error: Accessed Global component "