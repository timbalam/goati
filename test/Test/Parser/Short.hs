{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Test.Parser.Short
  ( tests
  )
  where

import Types.Parser.Short
import Types.Parser
import Parser( ShowMy(..) )

import Data.Function( (&) )
import Data.Foldable( traverse_ )
--import Control.Monad.Free
import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","
  

tests =
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
          
    , "variable" ~: let
        r = self_ "pub"
        e = (Var . Pub) (Ident "pub") :: Syntax
        in
          assertEqual (banner r) e r
        
    , "path" ~: let
        r = self_ "pub" #. "x" #. "y"
        e = Get (Get ((Var . Pub) (Ident "pub") `At` Ident "x") `At` Ident "y") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "negation" ~: let
        r = -(env_ "hi")
        e = (Unop Neg . Var) (Priv "hi") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "not" ~: let
        r = not_ (env_ "true")
        e = (Unop Not . Var) (Priv "true") :: Syntax
        in
          assertEqual (banner r) e r
        
    , "update" ~: let
        r = env_ "a" # block_ [ self_ "b" #= env_ "b" ]
        e = Var (Priv "a") `Extend` Rec [
          (SetPath . Pure .  Pub) (Ident "b") `SetRec` Var (Priv "b")
          ] :: Syntax
        in
          assertEqual (banner r) e r
        
    , "update path" ~: let
        r = env_ "a" #. "x" # block_ [ self_ "b" #= env_ "b" ] #. "y"
        e = Get ((Get ((Var) (Priv "a") `At` Ident "x") `Extend` Rec [
          (SetPath . Pure . Pub) (Ident "b") `SetRec` Var (Priv "b")
          ]) `At` Ident "y") :: Syntax
        in
          assertEqual (banner r) e r
          
    , "update with tup block" ~: assertFailure "##todo"
        
    , "block" ~:
      [  "rec private assignment" ~: let
          r = block_ [ env_ "a" #= env_ "b" ]
          e = (Block . Rec) [(SetPath . Pure) (Priv "a") `SetRec` Var (Priv "b")] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "rec private assignment to path" ~: let
          r = block_ [ env_ "a" #. "x" #= 1 ]
          e = (Block . Rec) [
            (SetPath . Free) (Pure (Priv "a") `At` Ident "x") `SetRec` IntegerLit 1
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "tup assignment" ~: let
          r = tup_ [ self_ "a" #= env_ "b" ]
          e = (Block . Tup) [Pure (Ident "a") `Set` Var (Priv "b")] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "tup assignment to path" ~: let
          r = tup_ [ self_ "a" #. "x" #= env_ "b" ]
          e = (Block . Tup) [
            Free (Pure (Ident "a") `At` Ident "x") `Set` Var (Priv "b")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned public assignment" ~: let
          r = tup_ [ self_ "pun" ]
          e = (Block . Tup) [(Pun . Pure . Pub) (Ident "pun")] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned private assignment" ~: let
          r = tup_ [ env_ "pun" ]
          e = (Block . Tup) [(Pun . Pure) (Priv "pun")] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "tup punned assignment to path" ~: let
          r = tup_ [ self_ "pun" #. "path" ]
          e = (Block . Tup) [
            (Pun . Free) ((Pure . Pub) (Ident "pun") `At` Ident "path")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "rec var declaration" ~: let
          r = block_ [ self_ "decl" ]
          e = (Block . Rec) [ DeclVar (Pure "decl") ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "rec path declaration" ~: let
          r = block_ [ self_ "decl" #. "x" ]
          e = (Block . Rec) [
            DeclVar (Free (Pure "decl" `At` Ident "x"))
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
            (SetPath . Pure) (Priv "var") `SetRec` IntegerLit 1,
            (SetPath . Free) (Pure (Priv "path") `At` Ident "f") `SetRec`
              ((Var) (Priv "var") & Binop Add $ IntegerLit 1),
            DeclVar (Pure "field")
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
            Pure (Ident "var") `Set` IntegerLit 1,
            Free (Pure (Ident "path") `At` Ident "f") `Set`
              (Var (Priv "var") & Binop Add $ IntegerLit 1),
            (Pun . Pure) (Priv "field")
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
              Pure (Ident "x") `Set` (SetPath . Pure . Pub) (Ident "y")
              ] `SetRec`
                Var (Priv "val")
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
              Free (Pure (Ident "x") `At` Ident "f") `Set`
                (SetPath . Free) (Pure (Priv "y") `At` Ident "f")
              ] `SetRec` Var (Priv "val")
            ] :: Syntax
          in
            assertEqual (banner r) e r
          
      , "destructure pun" ~: let
          r = block_ [
            tup_ [ env_ "y" #. "f" ] #=
              env_ "val"
            ]
          e = (Block . Rec) [
            Decomp [(Pun . Free) (Pure (Priv "y") `At` Ident "f")] `SetRec`
              Var (Priv "val")
            ] :: Syntax
          in
            assertEqual (banner r) e r
            
      , "destructure with remaining assigned" ~: let
          r = block_ [
            env_ "y" # tup_ [ self_ "f" #= env_ "x" ] #= env_ "z"
            ]
          e = (Block . Rec) [
            ((SetPath . Pure) (Priv "y") `SetDecomp` [
              Pure (Ident "f") `Set` SetPath (Pure (Priv "x"))
              ]) `SetRec` Var (Priv "z")
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
              (Pun . Free) (Pure (Priv "y") `At` Ident "f"),
              Free (Pure (Ident "y") `At` Ident "g") `Set` (SetPath . Pure) (Priv "g")
              ] `SetRec` Var (Priv "x")
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
            Decomp [ Pure (Ident "x") `Set`
              Decomp [ Pure (Ident "f") `Set` (SetPath . Pure) (Priv "f") ]
              ] `SetRec`
              (Block . Rec) [
                (SetPath . Free) ((Pure .Pub) (Ident "x") `At` Ident "f") `SetRec`
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
            (SetPath . Free) ((Pure . Pub) (Ident "x") `At` Ident "f") `SetRec` StringLit "abc",
            Decomp [(Pun . Pure) (Priv "a")] `SetRec` Get ((Var) (Priv "var") `At` Ident "f")
            ] :: Syntax
          in 
            assertEqual (banner r) e r
      ]
      
    ]