-- | My language exception machinery
module My.Types.Error
  ( DefnError(..)
  , MyError(..)
  , displayError
  ) where
  
import qualified My.Types.Syntax as P
import My.Types.Repr (Ident)
import Data.Foldable (foldr)
import Data.Typeable
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Text.Parsec
import Control.Exception
import Control.Monad.Catch (MonadThrow(..))

      
-- | Class for displaying exceptions
data MyError =
    DefnError DefnError
  | ScopeError ScopeError
  | KeyError KeyError
  | ParseError Text.Parsec.ParseError
  
  
displayError :: MyError -> String
displayError (DefnError e)  = displayDefnError e
displayError (ScopeError e) = displayScopeError e
displayError (KeyError e)   = displayKeyError e
displayError (ParseError e) = show e
displayError _              = "unknown error"


-- | Errors from binding definitions
data DefnError =
    OlappedMatch Ident
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet (P.Vis Ident Ident)
  -- ^ Error if a group assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately in a group
  deriving Eq
  
  
displayDefnError :: DefnError -> String
displayDefnError (OlappedMatch p) =
  "error: Multiple component matches: " ++ show p
displayDefnError (OlappedSet p) =
  "error: Multiple assignments: " ++ P.vis show show p
displayDefnError (OlappedVis i) =
  "error: Multiple visibilities: " ++ show i
  
  
newtype ScopeError = NotDefined Ident
  deriving Eq
  
displayScopeError :: ScopeError -> String
displayScopeError (NotDefined i) =
  "error: Missing assignment: " ++ show i

  
newtype KeyError k = NotComponent (Key k)
  deriving Eq
  
displayKeyError :: Show k => KeyError k -> String
displayKeyError (NotComponent k) =
  "error: Missing component: " ++ show k
