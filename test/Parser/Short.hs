{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Parser.Short
  ( shortTests
  )
  where

import My.Types.Parser.Short
import My.Types.Parser
import My.Parser (ShowMy(..))
import Data.Function( (&) )
import Data.Foldable( traverse_ )
import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","


type Syntax = Expr (Name Ident Key Import)
  

shortTests =
  test
    [ "integer literal" ~: let
        r = 20
        e = IntegerLit 20 :: Syntax
        in
          assertEqual (banner r) e r
          
    , "addition" ~: let
        r = 1 #+ 1
        e = IntegerLit 1 & Binop Add $ IntegerLit 1 :: Syntax
        in
          assertEqual (banner r) e r
          
    , "floating literal" ~: let
        r = 0.5
        e = NumberLit 0.5 :: Syntax
        in
          assertEqual (banner r) e r
          
    , "subtraction" ~: let
        r = 1.0 #- 2.0
        e = NumberLit 1 & Binop Sub $ NumberLit 2 :: Syntax
        in
          assertEqual (banner r) e r
    
    , "ops" ~:
        let
          ops =
            [ (Binop Add, (#+))
            , (Binop Sub, (#-))
            , (Binop Prod, (#*))
            , (Binop Div, (#/))
            , (Binop Pow, (#^))
            ]
          testop (o, f) = let
            e = IntegerLit 1 `o` IntegerLit 2 :: Syntax
            r = 1 `f` 2
            in
              assertEqual (banner r) e r
        in
          traverse_ testop ops
          
    , "comparisons" ~:
        let
          cmps = 
            [ (Binop Lt, (#<))
            , (Binop Le, (#<=))
            , (Binop Gt, (#>))
            , (Binop Ge, (#>=))
            , (Binop Eq, (#==))
            , (Binop Ne, (#!=))
            ]
          testcmp (o,  f) = let
            e = NumberLit 2 `o` NumberLit 0.2 :: Syntax
            r = 2.0 `f` 0.2
            in
              assertEqual (banner r) e r
        in
          traverse_ testcmp cmps
          
    , "string literal" ~: let
        r = "hello"
        e = StringLit "hello" :: Syntax
        in
          assertEqual (banner r) e r
          
          
    , "use import" ~: let
        r = use_ "hello"
        e = (Var . Ex) (Use "hello") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "variable" ~: let
        r = self_ "pub"
        e = (Var . In . Pub) (K_ "pub") :: Syntax
        in
          assertEqual (banner r) e r
        
    , "path" ~: let
        r = self_ "pub" #. "x" #. "y"
        e = Get (Get ((Var . In . Pub) (K_ "pub") `At` K_ "x") `At` K_ "y") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "negation" ~: let
        r = neg_ (env_ "hi")
        e = (Unop Neg . Var . In) (Priv "hi") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "not" ~: let
        r = not_ (env_ "true")
        e = (Unop Not . Var . In) (Priv "true") :: Syntax
        in
          assertEqual (banner r) e r
        
    , "update" ~: let
        r = env_ "a" # block_ [ self_ "b" #= env_ "b" ]
        e = (Var . In) (Priv "a") `Extend` Block [
          (LetPath . Pub . Pure) (K_ "b") `LetRec` (Var . In) (Priv "b")
          ] :: Syntax
        in
          assertEqual (banner r) e r
        
    , "update path" ~: let
        r = env_ "a" #. "x" # block_ [ self_ "b" #= env_ "b" ] #. "y"
        e = Get ((Get ((Var . In) (Priv "a") `At` K_ "x") `Extend` Block [
          (LetPath . Pub . Pure) (K_ "b") `LetRec` (Var . In) (Priv "b")
          ]) `At` K_ "y") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "update with tup block" ~: let
        r = env_ "a" # tup_ [ self_ "x" #= env_ "b" ]
        e = (Var . In) (Priv "a") `Extend` Tup [
          Pure (K_ "x") `Let` (Var . In) (Priv "b")
          ] :: Syntax
        in
          assertEqual (banner r) e r
          
    , "update with tup with multiple statements" ~: let
        r = env_ "a" # tup_ [ self_ "i" #= 4, self_ "j" #= env_ "x" ]
        e = (Var . In) (Priv "a") `Extend` Tup [
          Pure (K_ "i") `Let` IntegerLit 4,
          Pure (K_ "j") `Let` (Var . In) (Priv "x")
          ] :: Syntax
        in
          assertEqual (banner r) e r
        
    , "block" ~:
      [  "rec private assignment" ~: let
          r = block_ [ env_ "a" #= env_ "b" ]
          e = (Group . Block) [
            (LetPath . Priv) (Pure "a") `LetRec` (Var . In) (Priv "b")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "rec private assignment to path" ~: let
          r = block_ [ env_ "a" #. "x" #= 1 ]
          e = (Group . Block) [
            (LetPath . Priv . Free) (Pure "a" `At` K_ "x") `LetRec` IntegerLit 1
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "tup assignment" ~: let
          r = tup_ [ self_ "a" #= env_ "b" ]
          e = (Group . Tup) [Pure (K_ "a") `Let` (Var . In) (Priv "b")] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "tup assignment to path" ~: let
          r = tup_ [ self_ "a" #. "x" #= env_ "b" ]
          e = (Group . Tup) [
            Free (Pure (K_ "a") `At` K_ "x") `Let` (Var . In) (Priv "b")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned public assignment" ~: let
          r = tup_ [ self_ "pun" ]
          e = (Group . Tup) [(Pun . Pub . Pure) (K_ "pun")] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned private assignment" ~: let
          r = tup_ [ env_ "pun" ]
          e = (Group . Tup) [(Pun . Priv) (Pure "pun")] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned assignment to path" ~: let
          r = tup_ [ self_ "pun" #. "path" ]
          e = (Group . Tup) [
            (Pun . Pub . Free) (Pure (K_ "pun") `At` K_ "path")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "rec var declaration" ~: let
          r = block_ [ self_ "decl" ]
          e = (Group . Block) [ (Decl . Pure) (K_ "decl") ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "rec path declaration" ~: let
          r = block_ [ self_ "decl" #. "x" ]
          e = (Group . Block) [
            (Decl . Free) (Pure (K_ "decl" )`At` K_ "x")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "rec block with multiple statements" ~: let
          r = block_ [
            env_ "var" #= 1,
            env_ "path" #. "f" #=
              env_ "var" #+ 1,
            self_ "field" 
            ]
          e = (Group . Block) [
            (LetPath . Priv) (Pure "var") `LetRec` IntegerLit 1,
            (LetPath . Priv . Free) (Pure "path" `At` K_ "f") `LetRec`
              ((Var . In) (Priv "var") & Binop Add $ IntegerLit 1),
            (Decl . Pure) (K_ "field")
            ] :: Syntax
          in
            assertEqual (banner r) e r
        
      , "tup block with multiple statements" ~: let
          r = tup_ [
            self_ "var" #= 1,
            self_ "path" #. "f" #=
              env_ "var" #+ 1,
            env_ "field" 
            ]
          e = (Group . Tup) [
            Pure (K_ "var") `Let` IntegerLit 1,
            Free (Pure (K_ "path") `At` K_ "f") `Let`
              ((Var . In) (Priv "var") & Binop Add $ IntegerLit 1),
            (Pun . Priv) (Pure "field")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "destructure" ~: let
          r = block_ [
            tup_ [ self_ "x" #= self_ "y" ] #=
              env_ "val"
            ]
          e = (Group . Block) [
            Ungroup [
              Pure (K_ "x") `Let` (LetPath . Pub . Pure) (K_ "y")
              ] `LetRec`
                (Var . In) (Priv "val")
            ] :: Syntax
          in
          assertEqual (banner r) e r
          
      , "destructure path" ~: let
          r = block_ [
            tup_ [
              self_ "x" #. "f" #=
                env_ "y" #. "f"
              ] #= env_ "val"
            ]
          e = (Group . Block) [
            Ungroup [
              Free (Pure (K_ "x") `At` K_ "f") `Let`
                (LetPath . Priv . Free) (Pure "y" `At` K_ "f")
              ] `LetRec` (Var . In) (Priv "val")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "destructure pun" ~: let
          r = block_ [
            tup_ [ env_ "y" #. "f" ] #=
              env_ "val"
            ]
          e = (Group . Block) [
            Ungroup [(Pun . Priv . Free) (Pure "y" `At` K_ "f")]
              `LetRec` (Var . In) (Priv "val")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "destructure with remaining assigned" ~: let
          r = block_ [
            env_ "y" # tup_ [ self_ "f" #= env_ "x" ] #= env_ "z"
            ]
          e = (Group . Block) [
            ((LetPath . Priv) (Pure "y") `LetUngroup` [
              Pure (K_ "f") `Let` (LetPath . Priv) (Pure "x")
              ]) `LetRec` (Var . In) (Priv "z")
            ] :: Syntax
          in assertEqual (banner r) e r
            
      , "destructure with multiple statements" ~: let
          r = block_ [
            tup_ [
              env_ "y" #. "f",
              self_ "y" #. "g" #= env_ "g"
              ] #= env_ "x"
            ]
          e = (Group . Block) [
            Ungroup [
              (Pun . Priv . Free) (Pure "y" `At` K_ "f"),
              Free (Pure (K_ "y") `At` K_ "g") `Let` (LetPath . Priv) (Pure "g")
              ] `LetRec` (Var . In) (Priv "x")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "nested destructure" ~: let
          r = block_ [
            tup_ [ self_ "x" #=
              tup_ [ self_ "f" #= env_ "f" ]
              ] #=
                block_ [ self_ "x" #. "f" #= 1 ]
            ]
          e = (Group . Block) [
            Ungroup [ Pure (K_ "x") `Let`
              Ungroup [ Pure (K_ "f") `Let` (LetPath . Priv) (Pure "f") ]
              ] `LetRec`
              (Group . Block) [
                (LetPath . Pub . Free) (Pure (K_ "x") `At` K_ "f") `LetRec`
                  IntegerLit 1
                ]
            ] :: Syntax
          in
            assertEqual (banner r) e r
      
      , "block with destructure and other statements" ~: let
          r = block_ [
            self_ "x" #. "f" #= "abc",
            tup_ [ env_ "a" ] #= env_ "var" #. "f"
            ]
          e = (Group . Block) [
            (LetPath . Pub . Free) (Pure (K_ "x") `At` K_ "f") `LetRec` StringLit "abc",
            Ungroup [(Pun . Priv) (Pure "a")] `LetRec` Get ((Var . In) (Priv "var") `At` K_ "f")
            ] :: Syntax
          in 
            assertEqual (banner r) e r
      ]
      
    ]