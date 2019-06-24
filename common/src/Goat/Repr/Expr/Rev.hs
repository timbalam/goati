{-# LANGUAGE LambdaCase, OverloadedStrings, FlexibleContexts #-}
module Goat.Repr.Expr.Rev where

import Goat.Lang.Class
import Goat.Lang.Parser
  (CanonDefinition, CanonPattern, CanonExpr, unself)
import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.Dyn
import Goat.Util ((<&>))
import Bound
import Control.Applicative (Const(..))
import
  Control.Monad.State (get, put, State, evalState)
import Data.Bifoldable (bifoldMap)
import Data.Bitraversable (bisequenceA)
import Data.Function (on)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Void (Void, vacuous)

runRev
 :: MeasureExpr (DynCpts e Ident) v
 => Repr (DynCpts e Ident) v Void
 -> CanonExpr
runRev m
  = unself (revRepr (Names Set.empty) (vacuous m))

revRepr
 :: MeasureExpr (DynCpts e Ident) v
 => Names
 -> Repr
      (DynCpts e Ident)
      v
      (VarName NewIdent NewIdent (Import Ident))
 -> CanonDefinition
revRepr names
  = \case
    Var a
     -> revVar a
    
    Repr (Number d)
     -> fromRational (toRational d)
    
    Repr (Text t)
     -> quote_ (Text.unpack t)
    
    Repr (Bool b)
     -> if b
        then fromString "true"
        else fromString "false"
    
    Repr Null
     -> fromList []
    
    Repr (Comp (Memo v f))
     -> revExpr revRepr names f

revVar
 :: VarName NewIdent NewIdent (Import Ident)
 -> CanonDefinition
revVar (Left (Left (Local i))) = fromNewIdent i
revVar (Left (Right (Public i)))
  = "" #. fromNewIdent i
revVar (Right (Import i)) = use_ (fromIdent i)

revExpr
 :: Monad m
 => (Names
     -> m (VarName NewIdent NewIdent a)
     -> CanonDefinition)
 -> Names
 -> Expr
      (DynCpts e Ident)
      m
      (VarName NewIdent NewIdent a)
 -> CanonDefinition
revExpr revm names
  = \case
    Ext bs a -> revExtension revm names bs a
    Sel a n
     -> revm names a #. fromNewIdent (pubIdent n)
    Add a b -> on (#+) (revm names) a b
    Sub a b -> on (#-) (revm names) a b
    Mul a b -> on (#*) (revm names) a b
    Div a b -> on (#/) (revm names) a b
    Pow a b -> on (#^) (revm names) a b
    Eq a b -> on (#==) (revm names) a b
    Ne a b -> on (#!=) (revm names) a b
    Lt a b -> on (#<) (revm names) a b
    Le a b -> on (#<=) (revm names) a b
    Gt a b -> on (#>) (revm names) a b
    Ge a b -> on (#>=) (revm names) a b
    Or a b -> on (#||) (revm names) a b
    And a b -> on (#&&) (revm names) a b
    Not a -> not_ (revm names a)
    Neg a -> neg_ (revm names a)

revExtension
 :: Monad m
 => (Names
     -> m (VarName NewIdent NewIdent a)
     -> CanonDefinition)
 -> Names
 -> Bindings
      (DynCpts e Ident)
      (DynCpts e Ident)
      (Scope (Super Int) (Scope (Public Ident) m))
      (VarName NewIdent NewIdent a)
 -> m (VarName NewIdent NewIdent a)
 -> CanonDefinition
revExtension revm names bs m
  = evalState (mexpr (revm names m)) names
  where
  mexpr
   :: CanonDefinition
   -> State Names CanonDefinition
  mexpr e
    = do
      (kv, me)
       <- getConst
            (transverseBindings
              (\ (DynCpts kv me)
               -> Const
                    (Map.traverseWithKey
                      localName kv
                     <&> (flip (,) me)))
              bs)
      let
        ns = foldMap (pure . return . Left . Left) kv
        getsup (Super i) = ns !! i
        suppatt 
          = fromList
              (Map.foldMapWithKey 
                (\ pk (Local lk)
                 -> [fromPubIdent pk #=
                      fromNewIdent lk])
                kv)
        supstmts s = (suppatt, pure m):s
  
      stmts
       <- bindingstmts
            (instpub . instantiate getsup)
            (\ f c -> supstmts (f (cptstmts c)))
            bs
      
      names <- get
      let
        stmts'
         = map
            (\ (patt, em)
             -> patt #=
                  either
                    (\_ -> "undefined")
                    (revm names)
                    em)
            stmts
      
      return
        (maybe e (\_ -> "undefined") me #
          fromList stmts')
  
  instpub
    = instantiate
      (return . Left . Right . fmap pubIdent)

cptstmts
 :: DynCpts e Ident (m (VarName NewIdent NewIdent a))
 -> [(CanonPattern
     ,Either e (m (VarName NewIdent NewIdent a)))]
cptstmts (DynCpts kv _)
  = Map.foldMapWithKey
      (\ k ev -> [(fromPubIdent k, ev)])
      kv

bindingstmts
 :: (Functor f, Monad n)
 => (n (VarName NewIdent NewIdent a)
     -> m (VarName NewIdent NewIdent a))
 -> (([(CanonPattern
       ,Either e (m (VarName NewIdent NewIdent a)))]
      -> [(CanonPattern
          ,Either e
            (m (VarName NewIdent NewIdent a)))])
     -> f (m (VarName NewIdent NewIdent a))
     -> b)
 -> Bindings
      f
      (DynCpts e Ident)
      n
      (VarName NewIdent NewIdent a)
 -> State Names b
bindingstmts = go
  where
  go
   :: (Functor f, Monad n)
   => (n (VarName NewIdent NewIdent a)
       -> m (VarName NewIdent NewIdent a))
   -> (([(CanonPattern
         ,Either e 
            (m (VarName NewIdent NewIdent a)))]
       -> [(CanonPattern
           ,Either e
              (m (VarName NewIdent NewIdent a)))])
       -> f (m (VarName NewIdent NewIdent a))
       -> b)
   -> Bindings
        f
        (DynCpts e Ident)
        n
        (VarName NewIdent NewIdent a)
   -> State Names b
  go inst k (Match (DynCpts pkv me) mn bs)
    = do
      x@(Extend pkv' (Local rest))
       <- bisequenceA
            (Extend
              (Map.mapWithKey localName pkv)
              (newName me))
      let
        patt
          = fromNewIdent rest # fromList
              (Map.foldMapWithKey
                (\ pk (Local lk)
                 -> [fromPubIdent pk #=
                      fromNewIdent lk])
                pkv')
        ns
          = bifoldMap
              (pure . return . Left . Left)
              (pure . return . Left . Left)
              x
      go
        (inst . instantiate (get ns))
        (\ f
         -> k (\ s -> (patt, pure (inst mn)):f s))
        bs
  
  go inst k (Index bs)
    = do
      kv'
       <- getConst
            (transverseBindings
              (\ (Parts (DynCpts pkv _) _)
               -> Const
                    (Map.traverseWithKey
                      localName pkv))
              bs)
      let
        ns 
          = foldMap (pure . return . Left . Left) kv'
      
      go
        (inst . instantiate (get ns))
        (\ f (Parts (DynCpts pkv _) fv)
         -> k
              (\ s
               -> f (zipWith
                      (\ (Local n) ev
                       -> (fromNewIdent n, ev))
                      (foldMap pure kv')
                      (Map.elems pkv)
                       ++ s))
              fv)
        bs
  
  go inst k (Define fn)
    = return (k id (inst <$> fn))
  
  get ns (Local i) = ns !! i

  
--
newtype Names = Names (Set NewIdent)
newtype NewIdent = NewIdent Text deriving (Eq, Ord)

fromNewIdent :: IsString a => NewIdent -> a
fromNewIdent (NewIdent t)
  = fromString (Text.unpack t)

pubIdent :: Ident -> NewIdent
pubIdent i = NewIdent (Text.pack ('p':showIdent i))

fromPubIdent :: Field_ a => Ident -> a
fromPubIdent i = "" #. fromNewIdent (pubIdent i)

newName :: Maybe e -> State Names (Local NewIdent)
newName (Just _) = newLocalWith "restErr"
newName Nothing = newLocalWith "rest"

localName
  :: Ident
  -> Either e a
  -> State Names (Local NewIdent)
localName i (Left _)
  = newLocalWith (showIdent i ++ "Err")
localName i (Right _)
  = newLocalWith (showIdent i)

newLocalWith
 :: String -> State Names (Local NewIdent)
newLocalWith s
  = do
    Names nset <- get
    let
      i =
        head
          (filter
            (`Set.notMember` nset)
            (test s))
    put (Names (Set.insert i nset))
    return (Local i)
  where
  test s =
    NewIdent (Text.pack ('l':s))
      : map
          (\ i
            -> NewIdent
                (Text.pack
                  ('l':(s ++ show (i::Int)))))
          [0..]
