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
        r = -(env_ "hi")
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
        e = (Var . In) (Priv "a") `Extend` Rec [
          (SetPath . Pub . Pure) (K_ "b") `SetRec` (Var . In) (Priv "b")
          ] :: Syntax
        in
          assertEqual (banner r) e r
        
    , "update path" ~: let
        r = env_ "a" #. "x" # block_ [ self_ "b" #= env_ "b" ] #. "y"
        e = Get ((Get ((Var . In) (Priv "a") `At` K_ "x") `Extend` Rec [
          (SetPath . Pub . Pure) (K_ "b") `SetRec` (Var . In) (Priv "b")
          ]) `At` K_ "y") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "update with tup block" ~: let
        r = env_ "a" # tup_ [ self_ "x" #= env_ "b" ]
        e = (Var . In) (Priv "a") `Extend` Tup [
          Pure (K_ "x") `Set` (Var . In) (Priv "b")
          ] :: Syntax
        in
          assertEqual (banner r) e r
          
    , "update with tup with multiple statements" ~: let
        r = env_ "a" # tup_ [ self_ "i" #= 4, self_ "j" #= env_ "x" ]
        e = (Var . In) (Priv "a") `Extend` Tup [
          Pure (K_ "i") `Set` IntegerLit 4,
          Pure (K_ "j") `Set` (Var . In) (Priv "x")
          ] :: Syntax
        in
          assertEqual (banner r) e r
        
    , "block" ~:
      [  "rec private assignment" ~: let
          r = block_ [ env_ "a" #= env_ "b" ]
          e = (Block . Rec) [
            (SetPath . Priv) (Pure "a") `SetRec` (Var . In) (Priv "b")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "rec private assignment to path" ~: let
          r = block_ [ env_ "a" #. "x" #= 1 ]
          e = (Block . Rec) [
            (SetPath . Priv . Free) (Pure "a" `At` K_ "x") `SetRec` IntegerLit 1
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "tup assignment" ~: let
          r = tup_ [ self_ "a" #= env_ "b" ]
          e = (Block . Tup) [Pure (K_ "a") `Set` (Var . In) (Priv "b")] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "tup assignment to path" ~: let
          r = tup_ [ self_ "a" #. "x" #= env_ "b" ]
          e = (Block . Tup) [
            Free (Pure (K_ "a") `At` K_ "x") `Set` (Var . In) (Priv "b")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned public assignment" ~: let
          r = tup_ [ self_ "pun" ]
          e = (Block . Tup) [(Pun . Pub . Pure) (K_ "pun")] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned private assignment" ~: let
          r = tup_ [ env_ "pun" ]
          e = (Block . Tup) [(Pun . Priv) (Pure "pun")] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned assignment to path" ~: let
          r = tup_ [ self_ "pun" #. "path" ]
          e = (Block . Tup) [
            (Pun . Pub . Free) (Pure (K_ "pun") `At` K_ "path")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "rec var declaration" ~: let
          r = block_ [ self_ "decl" ]
          e = (Block . Rec) [ (DeclVar . Pure) (K_ "decl") ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "rec path declaration" ~: let
          r = block_ [ self_ "decl" #. "x" ]
          e = (Block . Rec) [
            (DeclVar . Free) (Pure (K_ "decl" )`At` K_ "x")
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
          e = (Block . Rec) [
            (SetPath . Priv) (Pure "var") `SetRec` IntegerLit 1,
            (SetPath . Priv . Free) (Pure "path" `At` K_ "f") `SetRec`
              ((Var . In) (Priv "var") & Binop Add $ IntegerLit 1),
            (DeclVar . Pure) (K_ "field")
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
          e = (Block . Tup) [
            Pure (K_ "var") `Set` IntegerLit 1,
            Free (Pure (K_ "path") `At` K_ "f") `Set`
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
          e = (Block . Rec) [
            Decomp [
              Pure (K_ "x") `Set` (SetPath . Pub . Pure) (K_ "y")
              ] `SetRec`
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
          e = (Block . Rec) [
            Decomp [
              Free (Pure (K_ "x") `At` K_ "f") `Set`
                (SetPath . Priv . Free) (Pure "y" `At` K_ "f")
              ] `SetRec` (Var . In) (Priv "val")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "destructure pun" ~: let
          r = block_ [
            tup_ [ env_ "y" #. "f" ] #=
              env_ "val"
            ]
          e = (Block . Rec) [
            Decomp [(Pun . Priv . Free) (Pure "y" `At` K_ "f")]
              `SetRec` (Var . In) (Priv "val")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "destructure with remaining assigned" ~: let
          r = block_ [
            env_ "y" # tup_ [ self_ "f" #= env_ "x" ] #= env_ "z"
            ]
          e = (Block . Rec) [
            ((SetPath . Priv) (Pure "y") `SetDecomp` [
              Pure (K_ "f") `Set` (SetPath . Priv) (Pure "x")
              ]) `SetRec` (Var . In) (Priv "z")
            ] :: Syntax
          in assertEqual (banner r) e r
            
      , "destructure with multiple statements" ~: let
          r = block_ [
            tup_ [
              env_ "y" #. "f",
              self_ "y" #. "g" #= env_ "g"
              ] #= env_ "x"
            ]
          e = (Block . Rec) [
            Decomp [
              (Pun . Priv . Free) (Pure "y" `At` K_ "f"),
              Free (Pure (K_ "y") `At` K_ "g") `Set` (SetPath . Priv) (Pure "g")
              ] `SetRec` (Var . In) (Priv "x")
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
          e = (Block . Rec) [
            Decomp [ Pure (K_ "x") `Set`
              Decomp [ Pure (K_ "f") `Set` (SetPath . Priv) (Pure "f") ]
              ] `SetRec`
              (Block . Rec) [
                (SetPath . Pub . Free) (Pure (K_ "x") `At` K_ "f") `SetRec`
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
          e = (Block . Rec) [
            (SetPath . Pub . Free) (Pure (K_ "x") `At` K_ "f") `SetRec` StringLit "abc",
            Decomp [(Pun . Priv) (Pure "a")] `SetRec` Get ((Var . In) (Priv "var") `At` K_ "f")
            ] :: Syntax
          in 
            assertEqual (banner r) e r
      ]
      
    ]