{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Test.Parser.Short
  ( tests
  )
  where

import Types.Parser.Short
import Types.Parser
import Types.Classes

import Data.Function( (&) )
import Data.Foldable( traverse_ )
--import Control.Monad.Free
import Test.HUnit hiding ( Label )
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","
  

tests =
  test
    [ "integer literal" ~: let
        r = 20
        e = IntegerLit 20 :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "addition" ~: let
        r = 1 #+ 1
        e = IntegerLit 1 & Binop Add $ IntegerLit 1 :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "floating literal" ~: let
        r = 0.5
        e = NumberLit 0.5 :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "subtraction" ~: let
        r = 1.0 #- 2.0
        e = NumberLit 1 & Binop Sub $ NumberLit 2 :: Syntax_
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
            e = IntegerLit 1 `o` IntegerLit 2 :: Syntax_
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
            e = NumberLit 2 `o` NumberLit 0.2 :: Syntax_
            r = 2.0 `f` 0.2
            in
              assertEqual (banner r) e r
        in
          traverse_ testcmp cmps
          
    , "string literal" ~: let
        r = "hello"
        e = StringLit "hello" :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "variable" ~: let
        r = self_ "pub"
        e = (Var . Pub) (Label "pub") :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "path" ~: let
        r = self_ "pub" #. "x" #. "y"
        e = Get (Get ((Var . Pub) (Label "pub") `At` Label "x") `At` Label "y") :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "negation" ~: let
        r = -(env_ "hi")
        e = (Unop Neg . Var) (Priv "hi") :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "not" ~: let
        r = not_ (env_ "true")
        e = (Unop Not . Var) (Priv "true") :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "update" ~: let
        r = env_ "a" # [ self_ "b" #= env_ "b" ]
        e = (Var) (Priv "a") `Extend` [
          (SetPath . Pure .  Pub) (Label "b") `Set` (Var) (Priv "b")
          ] :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "update path" ~: let
        r = env_ "a" #. "x" # [ self_ "b" #= env_ "b" ] #. "y"
        e = Get ((Get ((Var) (Priv "a") `At` Label "x") `Extend` [
          (SetPath . Pure . Pub) (Label "b") `Set` (Var) (Priv "b")
          ]) `At` Label "y") :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "block" ~: let
        r = Block [ env_ "a" #= env_ "b" ]
        e = Block [(SetPath . Pure) (Priv "a") `Set` (Var) (Priv "b")] :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "set path" ~: let
        r = Block [ env_ "a" #. "x" #= 1 ]
        e = Block [
          (SetPath . Free) (Pure (Priv "a") `At` Label "x") `Set` IntegerLit 1
          ] :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "set pun" ~: let
        r = Block [ self_ "pun" ]
        e = Block [(SetPun . Pure . Pub) (Label "pun")] :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "set pun path" ~: let
        r = Block [ self_ "pun" #. "path" ]
        e = Block [(SetPun . Free) ((Pure . Pub) (Label "pun") `At` Label "path")] :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "block with multiple statements" ~: let
        r = Block [
          env_ "var" #= 1,
          env_ "path" #. "f" #=
            env_ "var" #+ 1,
          self_ "field" 
          ]
        e = Block [
          (SetPath . Pure) (Priv "var") `Set` IntegerLit 1,
          (SetPath . Free) (Pure (Priv "path") `At` Label "f") `Set`
            ((Var) (Priv "var") & Binop Add $ IntegerLit 1),
          (SetPun . Pure . Pub) (Label "field")
          ] :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "destructure" ~: let
        r = Block [
          SetBlock [ self_ "x" #= self_ "y" ] #=
            env_ "val"
          ]
        e = Block [
          SetBlock [Pure (Label "x") `Match` (SetPath . Pure . Pub) (Label "y")] `Set`
            (Var) (Priv "val")
          ] :: Syntax_
        in
        assertEqual (banner r) e r
        
    , "destructure path" ~: let
        r = Block [
          SetBlock [
            self_ "x" #. "f" #=
              env_ "y" #. "f"
            ] #= env_ "val"
          ]
        e = Block [
          SetBlock [
            Free (Pure (Label "x") `At` Label "f") `Match`
              (SetPath . Free) (Pure (Priv "y") `At` Label "f")
            ] `Set` (Var) (Priv "val")
          ] :: Syntax_
        in
          assertEqual (banner r) e r
        
    , "destructure pun" ~: let
        r = Block [
          SetBlock [ env_ "y" #. "f" ] #=
            env_ "val"
          ]
        e = Block [
          SetBlock [(MatchPun . Free) (Pure (Priv "y") `At` Label "f")] `Set`
            (Var) (Priv "val")
          ] :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "destructure with remaining assigned" ~: let
        r = Block [
          [ self_ "f" #= env_ "x" ] #... env_ "y" #= env_ "z"
          ]
        e = Block [
          (SetDecomp . SetPath . Pure) (Priv "y") [
            Pure (Label "f") `Match` SetPath (Pure (Priv "x"))
            ] `Set` (Var) (Priv "z")
          ] :: Syntax_
        in assertEqual (banner r) e r
          
    , "destructure with multiple statements" ~: let
        r = Block [
          SetBlock [
            env_ "y" #. "f",
            self_ "y" #. "g" #= env_ "g"
            ] #= env_ "x"
          ]
        e = Block [
          SetBlock [
            (MatchPun . Free) (Pure (Priv "y") `At` Label "f"),
            Free (Pure (Label "y") `At` Label "g") `Match` (SetPath . Pure) (Priv "g")
            ] `Set` (Var) (Priv "x")
          ] :: Syntax_
        in
          assertEqual (banner r) e r
          
    , "nested destructure" ~: let
        r = Block [
          SetBlock [ self_ "x" #=
            SetBlock [ self_ "f" #= env_ "f" ]
            ] #=
            Block [
              self_ "x" #. "f" #=
                1
              ]
          ]
        e = Block [
          SetBlock [ Pure (Label "x") `Match`
            SetBlock [ Pure (Label "f") `Match` (SetPath . Pure) (Priv "f") ]
            ] `Set`
            Block [
              (SetPath . Free) ((Pure .Pub) (Label "x") `At` Label "f") `Set`
                IntegerLit 1
              ]
          ] :: Syntax_
        in
          assertEqual (banner r) e r
    
    , "block with destructure and other statements" ~: let
        r = Block [
          self_ "x" #. "f" #= "abc",
          SetBlock [ env_ "a" ] #= env_ "var" #. "f"
          ]
        e = Block [
          (SetPath . Free) ((Pure . Pub) (Label "x") `At` Label "f") `Set` StringLit "abc",
          SetBlock [(MatchPun . Pure) (Priv "a")] `Set` Get ((Var) (Priv "var") `At` Label "f")
          ] :: Syntax_
        in 
          assertEqual (banner r) e r
    ]