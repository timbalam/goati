{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes, TypeFamilies #-}

module Syntax.Class.Type
  ( tests
  )
  where

import My.Types.Syntax.Class hiding (Expr)
import My.Syntax.Parser (Printer, showP)
import My.Types.Parser
import Data.String (IsString)
import Data.Function( (&) )
import Data.Foldable( traverse_ )
import Test.HUnit
  
  
banner :: Printer -> String
banner p = "For " ++ showP p ","


type S = Expr (Name Ident Key Import)
  

tests =
  test
    [ "integer literal" ~: let
        r :: Num a => a
        r = 20
        e :: S
        e = IntegerLit 20
        in assertEqual (banner r) e r
          
    , "addition" ~: let
        r :: (Num a, Lit a) => a
        r = 1 #+ 1
        e :: S
        e = IntegerLit 1 & Binop Add $ IntegerLit 1
        in assertEqual (banner r) e r
          
    , "floating literal" ~: let
        r :: Fractional a => a
        r = 0.5
        e :: S
        e = NumberLit 0.5
        in
          assertEqual (banner r) e r
          
    , "subtraction" ~: let
        r :: (Fractional a, Lit a) => a
        r = 1.0 #- 2.0
        e :: S
        e = NumberLit 1 & Binop Sub $ NumberLit 2
        in
          assertEqual (banner r) e r
    
    , "ops" ~:
        let
          testop
            :: (S -> S -> S) -> (forall a . Lit a => a -> a -> a) -> Assertion
          testop o f = let
            e :: S
            e = IntegerLit 1 `o` IntegerLit 2
            r :: (Num a, Lit a) => a
            r = 1 `f` 2
            in
              assertEqual (banner r) e r
        in do
          testop (Binop Add) (#+)
          testop (Binop Sub) (#-)
          testop (Binop Prod) (#*)
          testop (Binop Div) (#/)
          testop (Binop Pow) (#^)
          
    , "comparisons" ~:
        let
          testcmp
            :: (S -> S -> S) -> (forall a. Lit a => a -> a -> a) -> Assertion
          testcmp o f = let
            e :: S
            e = NumberLit 2 `o` NumberLit 0.2
            r :: (Fractional a, Lit a) => a
            r = 2.0 `f` 0.2
            in
              assertEqual (banner r) e r
        in do
          testcmp (Binop Lt) (#<)
          testcmp (Binop Le) (#<=)
          testcmp (Binop Gt) (#>)
          testcmp (Binop Ge) (#>=)
          testcmp (Binop Eq) (#==)
          testcmp (Binop Ne) (#!=)
          
    , "string literal" ~: let
        r :: IsString a => a
        r = "hello"
        e :: S
        e = TextLit "hello"
        in
          assertEqual (banner r) e r
          
          
    , "use import" ~: let
        r :: Extern a => a
        r = use_ "hello"
        e :: S
        e = (Var . Ex) (Use "hello")
        in assertEqual (banner r) e r
          
    , "variable" ~: let
        r :: Self a => a
        r = self_ "pub"
        e :: S
        e = (Var . In . Pub) (K_ "pub")
        in assertEqual (banner r) e r
        
    , "path" ~: let
        r :: RelPath a => a
        r = self_ "pub" #. "x" #. "y"
        e :: S
        e = Get (Get ((Var . In . Pub) (K_ "pub") `At` K_ "x") `At` K_ "y")
        in assertEqual (banner r) e r
          
    , "negation" ~: let
        r :: (Local a, Lit a) => a
        r = neg_ (local_ "hi")
        e :: S
        e = (Unop Neg . Var . In) (Priv "hi")
        in assertEqual (banner r) e r
          
    , "not" ~: let
        r :: (Local a, Lit a) => a
        r = not_ (local_ "true")
        e :: S
        e = (Unop Not . Var . In) (Priv "true")
        in assertEqual (banner r) e r
        
    , "update" ~: let
        r :: Syntax a => a
        r = local_ "a" # block_ (self_ "b" #= local_ "b")
        e :: S
        e = (Var . In) (Priv "a") `Extend` Block [
          (LetPath . Pub . Pure) (K_ "b") `LetRec` (Var . In) (Priv "b")
          ] :: S
        in assertEqual (banner r) e r
        
    , "update path" ~: let
        r :: Syntax a => a
        r = local_ "a" #. "x" # block_ (self_ "b" #= local_ "b") #. "y"
        e :: S
        e = Get ((Get ((Var . In) (Priv "a") `At` K_ "x") `Extend` Block [
          (LetPath . Pub . Pure) (K_ "b") `LetRec` (Var . In) (Priv "b")
          ]) `At` K_ "y")
        in assertEqual (banner r) e r
          
    , "update with tup block" ~: let
        r :: Syntax a => a
        r = local_ "a" # tup_ (self_ "x" #= local_ "b")
        e :: S
        e = (Var . In) (Priv "a") `Extend` Tup [
          Pure (K_ "x") `Let` (Var . In) (Priv "b")
          ]
        in assertEqual (banner r) e r
          
    , "update with tup with multiple statements" ~: let
        r :: Syntax a => a
        r = local_ "a" # tup_ (self_ "i" #= 4 #: self_ "j" #= local_ "x")
        e :: S
        e = (Var . In) (Priv "a") `Extend` Tup [
          Pure (K_ "i") `Let` IntegerLit 4,
          Pure (K_ "j") `Let` (Var . In) (Priv "x")
          ]
        in assertEqual (banner r) e r
        
    , "block" ~:
      [  "rec private assignment" ~: let
          r :: Syntax a => a
          r = block_ (local_ "a" #= local_ "b")
          e :: S
          e = (Group . Block) [
            (LetPath . Priv) (Pure "a") `LetRec` (Var . In) (Priv "b")
            ]
          in assertEqual (banner r) e r
          
      , "rec private assignment to path" ~: let
          r :: Syntax a => a
          r = block_ (local_ "a" #. "x" #= 1)
          e :: S
          e = (Group . Block) [
            (LetPath . Priv . Free) (Pure "a" `At` K_ "x") `LetRec` IntegerLit 1
            ]
          in assertEqual (banner r) e r
            
      , "tup assignment" ~: let
          r :: Syntax a => a
          r = tup_ (self_ "a" #= local_ "b")
          e :: S
          e = (Group . Tup) [Pure (K_ "a") `Let` (Var . In) (Priv "b")]
          in assertEqual (banner r) e r
            
      , "tup assignment to path" ~: let
          r :: Syntax a => a
          r = tup_ (self_ "a" #. "x" #= local_ "b")
          e :: S
          e = (Group . Tup) [
            Free (Pure (K_ "a") `At` K_ "x") `Let` (Var . In) (Priv "b")
            ]
          in assertEqual (banner r) e r
          
      , "tup punned public assignment" ~: let
          r :: Syntax a => a
          r = tup_ (self_ "pun")
          e :: S
          e = (Group . Tup) [(Pun . Pub . Pure) (K_ "pun")]
          in assertEqual (banner r) e r
          
      , "tup punned private assignment" ~: let
          r :: Syntax a => a
          r = tup_ (local_ "pun")
          e :: S
          e = (Group . Tup) [(Pun . Priv) (Pure "pun")]
          in assertEqual (banner r) e r
          
      , "tup punned assignment to path" ~: let
          r :: Syntax a => a
          r = tup_ (self_ "pun" #. "path")
          e :: S
          e = (Group . Tup) [
            (Pun . Pub . Free) (Pure (K_ "pun") `At` K_ "path")
            ]
          in assertEqual (banner r) e r
            
      , "rec var declaration" ~: let
          r :: Syntax a => a
          r = block_ (self_ "decl")
          e :: S
          e = (Group . Block) [ (Decl . Pure) (K_ "decl") ] :: S
          in
            assertEqual (banner r) e r
            
      , "rec path declaration" ~: let
          r :: Syntax a => a
          r = block_ (self_ "decl" #. "x")
          e :: S
          e = (Group . Block) [
            (Decl . Free) (Pure (K_ "decl" )`At` K_ "x")
            ]
          in
            assertEqual (banner r) e r
          
      , "rec block with multiple statements" ~: let
          r :: Syntax a => a
          r = block_
            ( local_ "var" #= 1
            #: local_ "path" #. "f" #= local_ "var" #+ 1
            #: self_ "field"
            )
          e :: S
          e = (Group . Block) [
            (LetPath . Priv) (Pure "var") `LetRec` IntegerLit 1,
            (LetPath . Priv . Free) (Pure "path" `At` K_ "f") `LetRec`
              ((Var . In) (Priv "var") & Binop Add $ IntegerLit 1),
            (Decl . Pure) (K_ "field")
            ]
          in assertEqual (banner r) e r
        
      , "tup block with multiple statements" ~: let
          r :: Syntax a => a
          r = tup_ 
            ( self_ "var" #= 1
            #: self_ "path" #. "f" #= local_ "var" #+ 1
            #: local_ "field" 
            )
          e :: S
          e = (Group . Tup) [
            Pure (K_ "var") `Let` IntegerLit 1,
            Free (Pure (K_ "path") `At` K_ "f") `Let`
              ((Var . In) (Priv "var") & Binop Add $ IntegerLit 1),
            (Pun . Priv) (Pure "field")
            ]
          in assertEqual (banner r) e r
            
      , "destructure" ~: let
          r :: Syntax a => a
          r = block_
            ( tup_ (self_ "x" #= self_ "y") #= local_ "val"
            )
          e :: S
          e = (Group . Block) [
            Ungroup [
              Pure (K_ "x") `Let` (LetPath . Pub . Pure) (K_ "y")
              ] `LetRec`
                (Var . In) (Priv "val")
            ]
          in
          assertEqual (banner r) e r
          
      , "destructure path" ~: let
          r :: Syntax a => a
          r = block_
            ( tup_ 
              ( self_ "x" #. "f" #= local_ "y" #. "f"
              ) #= local_ "val"
            )
          e :: S
          e = (Group . Block) [
            Ungroup [
              Free (Pure (K_ "x") `At` K_ "f") `Let`
                (LetPath . Priv . Free) (Pure "y" `At` K_ "f")
              ] `LetRec` (Var . In) (Priv "val")
            ]
          in
            assertEqual (banner r) e r
          
      , "destructure pun" ~: let
          r :: Syntax a => a
          r = block_
            ( tup_ (local_ "y" #. "f") #= local_ "val"
            )
          e :: S
          e = (Group . Block) [
            Ungroup [(Pun . Priv . Free) (Pure "y" `At` K_ "f")]
              `LetRec` (Var . In) (Priv "val")
            ]
          in assertEqual (banner r) e r
            
      , "destructure with remaining assigned" ~: let
          r :: Syntax a => a
          r = block_
            ( local_ "y" # tup_ (self_ "f" #= local_ "x") #= local_ "z"
            )
          e :: S
          e = (Group . Block) [
            ((LetPath . Priv) (Pure "y") `LetUngroup` [
              Pure (K_ "f") `Let` (LetPath . Priv) (Pure "x")
              ]) `LetRec` (Var . In) (Priv "z")
            ]
          in assertEqual (banner r) e r
            
      , "destructure with multiple statements" ~: let
          r :: Syntax a => a
          r = block_
            ( tup_
              ( local_ "y" #. "f"
              #: self_ "y" #. "g" #= local_ "g"
              ) #= local_ "x"
            )
          e :: S
          e = (Group . Block) [
            Ungroup [
              (Pun . Priv . Free) (Pure "y" `At` K_ "f"),
              Free (Pure (K_ "y") `At` K_ "g") `Let` (LetPath . Priv) (Pure "g")
              ] `LetRec` (Var . In) (Priv "x")
            ]
          in assertEqual (banner r) e r
            
      , "nested destructure" ~: let
          r :: Syntax a => a
          r = block_
            ( tup_ 
              ( self_ "x" #=
                tup_ (self_ "f" #= local_ "f")
              ) #=
                block_ (self_ "x" #. "f" #= 1)
            )
          e :: S
          e = (Group . Block) [
            Ungroup [ Pure (K_ "x") `Let`
              Ungroup [ Pure (K_ "f") `Let` (LetPath . Priv) (Pure "f") ]
              ] `LetRec`
              (Group . Block) [
                (LetPath . Pub . Free) (Pure (K_ "x") `At` K_ "f") `LetRec`
                  IntegerLit 1
                ]
            ]
          in assertEqual (banner r) e r
      
      , "block with destructure and other statements" ~: let
          r :: Syntax a => a
          r = block_
            ( self_ "x" #. "f" #= "abc"
            #: tup_ (local_ "a") #= local_ "var" #. "f"
            )
          e :: S
          e = (Group . Block) [
            (LetPath . Pub . Free) (Pure (K_ "x") `At` K_ "f") `LetRec` TextLit "abc",
            Ungroup [(Pun . Priv) (Pure "a")] `LetRec` Get ((Var . In) (Priv "var") `At` K_ "f")
            ]
          in assertEqual (banner r) e r
      ]
      
    ]