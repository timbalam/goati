module Goat.Repr.Expr.Rev where

import Goat.Lang.Parser
import Goat.Repr.Expr


type Names = [Ident]

revRepr
 :: Names
 -> Repr
      (DynCpts e Ident)
      v
      (VarName Ident Ident (Import Ident))
 -> CanonExpr
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
        then fromString "Bool.true"
        else fromString "Bool.false"
    
    Repr Null
     -> fromList []
    
    Repr (Comp (Memo v f))
     -> revExpr names f

revVar
 :: VarName Ident Ident (Import Ident)
 -> CanonExpr
revVar (Left (Left (Local i))) = fromIdent i
revVar (Left (Right (Public i))) = "" #. fromIdent i
revVar (Right (Import i)) = use_ (fromIdent i)

revExpr
 :: (Names -> m a -> CanonExpr)
 -> Names
 -> Expr (DynCpts e Ident) m a
 -> CanonExpr
revExpr revm names
  = \case
    Ext bs a -> revExtension revm names a bs
    Sel a n -> revm names a #. fromIdent n
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
 :: (Names -> m a -> CanonExpr)
 -> Names
 -> Bindings
      (DynCpts e Ident) (DynCpts e Ident) m a
 -> m a
 -> CanonExpr
revBindings revm names m
  = go []
  where
  go stmts (Match (DynCpts pkv pme) mm bs)
    = do
      Extend kv' rest
       <- traverse
            (Extend
              (Map.withKey (\ k _ -> toName k) kv)
              newName)
      let
        oldnewks = Map.keys kv' 
        patt
          = rest # fromList
              [ if oldk == newk
                then fromIdent oldk
                else "" #. fromIdent oldk #=
                      fromIdent newk 
              | (oldk, newk) <- oldnewks
              ]
      go [(patt, mm)] bs
  
    Define (DynCpts kv me)
     -> maybe 
          (revm names m)
          (\_ -> "undefined")
          me # revmMap rem names kv
    
    Match (DynCpts pkv pme) mm bs
     -> 

  where
  revMap
   :: ([Ident] -> a -> CanonExpr)
   -> [Ident]
   -> Map Ident (Either e a)
   -> CanonExpr
  revMap reva names kv
    = fromList
        (Map.foldMapWithKey
          (\ k ea
           -> [ fromIdent k #= either
                  (\_ -> "undefined")
                  (reva names)
                  ea
              ])
          kv)