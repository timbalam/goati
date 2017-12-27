{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Test.Parser.Short
  ( tests
  )
  where

import Types.Parser.Short
import Types.Classes

import Data.Function( (&) )
import Data.Foldable( traverse_ )
import Control.Monad.Free
import Test.HUnit hiding ( Label )
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","
  
  
type E = Syntax


tests =
  test
    [ "integer literal" ~: let
        r = 20 :: E
        e = IntegerLit 20
        in
          assertEqual (banner r) e r
          
    , "addition" ~: let
        r = 1 #+ 1 :: E
        e = IntegerLit 1 & Binop Add $ IntegerLit 1
        in
          assertEqual (banner r) e r
          
    , "floating literal" ~: let
        r = 0.5 :: E
        e = NumberLit 0.5
        in
          assertEqual (banner r) e r
          
    , "subtraction" ~: let
        r = 1.0 #- 2.0 :: E
        e = NumberLit 1 & Binop Sub $ NumberLit 2
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
            e = IntegerLit 1 `o` IntegerLit 2
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
            e = NumberLit 2 `o` NumberLit 0.2
            r = 2.0 `f` 0.2
            in
              assertEqual (banner r) e r
        in
          traverse_ testcmp cmps
          
    , "string literal" ~: let
        r = "hello" :: E
        e = StringLit "hello"
        in
          assertEqual (banner r) e r
          
    , "variable" ~: let
        r = self' "pub" :: E
        e = (Var . Intern . Pub) (Label "pub")
        in
          assertEqual (banner r) e r
        
    , "path" ~: let
        r = self' "pub" #. "x" #. "y" :: E
        e = Get (Get ((Var . Intern . Pub) (Label "pub") `At` Label "x") `At` Label "y")
        in
          assertEqual (banner r) e r
          
    , "negation" ~: let
        r = -(env' "hi") :: E
        e = (Unop Neg . Var . Intern) (Priv "hi")
        in
          assertEqual (banner r) e r
          
    , "not" ~: let
        r = not' (env' "true") :: E
        e = (Unop Not . Var . Intern) (Priv "true")
        in
          assertEqual (banner r) e r
        
    , "update" ~: let
        r = env' "a" # env' "b" :: E
        e = (Var . Intern) (Priv "a") `Update` (Var . Intern) (Priv "b")
        in
          assertEqual (banner r) e r
        
    , "update path" ~: let
        r = env' "a" #. "x" # env' "b" #. "y" :: E
        e = Get ((Get ((Var . Intern) (Priv "a") `At` Label "x") `Update` (Var . Intern) (Priv "b")) `At` Label "y")
        in
          assertEqual (banner r) e r
        
    , "block" ~: let
        r = block' [ env' "a" #= env' "b" ] :: E
        e = Block [(SetPath . Pure) (Priv "a") `Set` (Var . Intern) (Priv "b")] Nothing
        in
          assertEqual (banner r) e r
        
    , "set path" ~: let
        r = block' [ env' "a" #. "x" #= 1 ] :: E
        e = Block [
          (SetPath . Free) (Pure (Priv "a") `At` Label "x") `Set` IntegerLit 1
          ] Nothing
        in
          assertEqual (banner r) e r
        
    , "set pun" ~: let
        r = block' [ self' "pun" ] :: E
        e = Block [(SetPun . Pure . Pub) (Label "pun")] Nothing
        in
          assertEqual (banner r) e r
        
    , "set pun path" ~: let
        r = block' [ self' "pun" #. "path" ] :: E
        e = Block [(SetPun . Free) ((Pure . Pub) (Label "pun") `At` Label "path")] Nothing
        in
          assertEqual (banner r) e r
        
    , "block with multiple statements" ~: let
        r = block' [
          env' "var" #= 1,
          env' "path" #. "f" #=
            env' "var" #+ 1,
          self' "field" 
          ] :: E
        e = Block [
          (SetPath . Pure) (Priv "var") `Set` IntegerLit 1,
          (SetPath . Free) (Pure (Priv "path") `At` Label "f") `Set`
            ((Var . Intern) (Priv "var") & Binop Add $ IntegerLit 1),
          (SetPun . Pure . Pub) (Label "field")
          ] Nothing
        in
          assertEqual (banner r) e r
        
    , "destructure" ~: let
        r = block' [
          setblock' [ self' "x" #= self' "y" ] #=
            env' "val"
          ] :: E
        e = Block [
          SetBlock [Pure (Label "x") `Match` (SetPath . Pure . Pub) (Label "y")] Nothing `Set`
            (Var . Intern) (Priv "val")
          ] Nothing
        in
        assertEqual (banner r) e r
        
    , "destructure path" ~: let
        r = block' [
          setblock' [
            self' "x" #. "f" #=
              env' "y" #. "f"
            ] #= env' "val"
          ] :: E
        e = Block [
          SetBlock [
            Free (Pure (Label "x") `At` Label "f") `Match`
              (SetPath . Free) (Pure (Priv "y") `At` Label "f")
            ] Nothing `Set` (Var . Intern) (Priv "val")
          ] Nothing
        in
          assertEqual (banner r) e r
        
    , "destructure pun" ~: let
        r = block' [
          setblock' [ env' "y" #. "f" ] #=
            env' "val"
          ] :: E
        e = Block [
          SetBlock [(MatchPun . Free) (Pure (Priv "y") `At` Label "f")] Nothing `Set`
            (Var . Intern) (Priv "val")
          ] Nothing
        in
          assertEqual (banner r) e r
          
    , "destructure with multiple statements" ~: let
        r = block' [
          setblock' [
            env' "y" #. "f",
            self' "y" #. "g" #= env' "g"
            ] #= env' "x"
          ] :: E
        e = Block [
          SetBlock [
            (MatchPun . Free) (Pure (Priv "y") `At` Label "f"),
            Free (Pure (Label "y") `At` Label "g") `Match` (SetPath . Pure) (Priv "g")
            ] Nothing `Set` (Var . Intern) (Priv "x")
          ] Nothing
        in
          assertEqual (banner r) e r
          
    , "nested destructure" ~: let
        r = block' [
          setblock' [ self' "x" #=
            setblock' [ self' "f" #= env' "f" ]
            ] #=
            block' [
              self' "x" #. "f" #=
                1
              ]
          ] :: E
        e = Block [
          SetBlock [ Pure (Label "x") `Match`
            SetBlock [ Pure (Label "f") `Match` (SetPath . Pure) (Priv "f") ] Nothing
            ] Nothing `Set`
            Block [
              (SetPath . Free) ((Pure .Pub) (Label "x") `At` Label "f") `Set`
                IntegerLit 1
              ] Nothing
          ] Nothing
        in
          assertEqual (banner r) e r
    
    , "block with destructure and other statements" ~: let
        r = block' [
          self' "x" #. "f" #= "abc",
          setblock' [ env' "a" ] #= env' "var" #. "f"
          ] :: E
        e = Block [
          (SetPath . Free) ((Pure . Pub) (Label "x") `At` Label "f") `Set` StringLit "abc",
          SetBlock [(MatchPun . Pure) (Priv "a")] Nothing `Set` Get ((Var . Intern) (Priv "var") `At` Label "f")
          ] Nothing
        in 
          assertEqual (banner r) e r
    ]