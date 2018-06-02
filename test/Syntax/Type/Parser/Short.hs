{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Syntax.Type.Parser.Short
  ( tests
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
  

tests =
  test
    [ "block" ~:
      [  "rec var declaration" ~: let
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