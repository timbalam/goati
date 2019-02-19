{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Syntax.Eval
  ( tests )
  where

import Goat.Syntax.Class
import Goat.Error
import Goat.Syntax.Parser (Printer, showP)
import Data.Void (Void)
import Test.HUnit

import Debug.Trace
  
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


parses :: Either [DefnError Ident] a -> IO a
parses = either 
  (fail . displayErrorList displayDefnError)
  return
  
  
fails
  :: Show a
  => ([DefnError Ident] -> Assertion)
  -> Either [DefnError Ident] a -> Assertion
fails f = either f (fail . showString "Unexpected: " . show)

tests
  :: (Expr a, Lit b, IsString b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test
tests expr = test
  [ "literals" ~: literals expr
  , "blocks" ~: blocks expr
  , "scope" ~: scope expr
  , "paths" ~: paths expr
  --, "escape" ~: escape expr
  , "extension" ~: extension expr
  , "patterns" ~: patterns expr
  ]

literals
  :: (Lit a, Lit b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test
literals expr = test
  [ "add" ~: let
      r :: (Num a, Lit a) => a
      r = (1 #+ 1)
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "subtract" ~: let
      r :: (Num a, Lit a) => a
      r = (1 #- 2)
      e = fromInteger (-1)
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "mixed" ~: let
      r :: (Num a, Lit a) => a
      r = 1 #+ 1 #* 2 #- 2
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "comparisons" ~: let
      r :: (Num a, Lit a) => a
      r = 3 #> 2
      e = 2 #<= 3
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "equality" ~: let
      r :: (Num a, Lit a) => a
      r = 2 #!= 2
      e = not_ (2 #== 2)
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
  
  ]
      
blocks
  :: (Expr a, Lit b, IsString b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test      
blocks expr = test 
  [ "publicly declared component can be accessed" ~: let
      r :: Expr a => a
      r = block_ [ "" #. "pub" #= 1 ] #. "pub"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
     
  , "locally declared component is not accesssible ##todo type error" ~: let
      r :: Expr a => a
      r = block_ [ "priv" #= 1 ] #. "priv"
      in parses (expr r) >>= assertFailure . show
      
  , "values with multiple declared components return the corresponding value when a component is accessed" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= 1
        , "" #. "b" #= 2
        , "" #. "c" #= "xy"
        ] #. "c"
      e = "xy"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "components values are independent of declaration order" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "c" #= "xy"
        , "" #. "a" #= 1
        , "" #. "b" #= 2
        ] #. "c"
      e = "xy"
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "component definition can reference previous private assignment in same scope" ~: let
      r :: Expr a => a
      r = block_
        [ "priv" #= 1
        , "" #. "pub" #= "priv"
        ] #. "pub"
      e = 1
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "component definition can reference later private assignment in same scope" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "pub" #= "priv"
        , "priv" #= 1
        ] #. "pub"
      e = 1
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "component can reference earlier public assignment from same scope" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "b" #= 2
        , "" #. "a" #= "" #. "b"
        ] #. "a"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "component can reference to later public assignment from same scope" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= "" #. "b"
        , "" #. "b" #= 2
        ] #. "a"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "public definition can be reference via a private alias" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= 1
        , "" #. "b" #= "a"
        ] #. "b"
      e = 1
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "component can transitively reference a public assignment via a privately declared reference" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "public" #= 1
        , "notPublic" #= "" #. "public"
        , "" #. "x" #= "notPublic"
        ] #. "x"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "component can reference an unbound variable" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= 2
        , "" #. "b" #= "c"
        ] #. "b"
      e = "c"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "type error when transitively accessing an undeclared public field ##todo type error" ~: let
      r :: Expr a => a
      r = block_ [ "" #. "b" #= "" #. "a" ] #. "b"
      in parses (expr r) >>= assertFailure . show
  
  , "component access does not execute unrelated components" ~: let
      r :: Expr a => a
      r = block_
        [ "selfRef" #= "selfRef"
        , "" #. "x" #= 2
        , "" #. "loop" #= "selfRef"
        ] #. "x"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "cannot assign private variable twice" ~: let
      r :: Expr a => a
      r = block_
        [ "a" #= 1
        , "a" #= "hello"
        ]
      e = [OlappedSet ("a")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "cannot assign public variable twice" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "x" #= 1
        , "" #. "x" #= "a"
        ]
      e = [OlappedSet ("" #. "x")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "cannot assign same public and private variable" ~: let
      r :: Expr a => a
      r = block_
        [ "a" #= "first"
        , "" #. "a" #= "second"
        ]
      e = [OlappedVis ("a")]
      in fails (assertEqual (banner r) e) (expr r)
    
  , "block component definitions be self-referential" ~: let
      r :: Expr a => a
      r = block_
        [ "y" #= block_
          [ "" #. "a" #= "y" #. "b"
          , "" #. "b" #= 1
          ]
        , "" #. "call" #= "y" #. "a"
        ] #. "call"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
  ]


scope
  :: (Expr a, Lit b, IsString b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test
scope expr = test  
  [ "component can access public components of nested blocks" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "return" #=
            block_ [ "" #. "return" #= "str" ] #. "return"
        ] #. "return"
      e = "str"
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "components can access nested components via reference to local assignment in same scope" ~: let
      r :: Expr a => a
      r = block_
        [ "object" #= block_ [ "" #. "b" #= 1 ]
        , "" #. "c" #= "object" #. "b"
        ] #. "c"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "nested block definitions can reference outer public definitions via private alias" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= 1
        , "object" #=
            block_ [ "" #. "b" #= "a" ]
        , "" #. "c" #= "object" #. "b"
        ] #. "c"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "nested block private assignments shadows private assignment of outer scope" ~: let
      r :: Expr a => a
      r = block_
        [ "outer" #= 1
        , "" #. "inner" #= block_
          [ "outer" #= 2
          , "" #. "shadow" #= "outer"
          ] #. "shadow"
        ] #. "inner"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "nested block private assignment shadows private alias for outer public assignment" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "outer" #= "hello"
        , "" #. "inner" #= block_
          [ "" #. "shadow" #= "outer"
          , "outer" #= "bye"
          ] #. "shadow"
        ] #. "inner"
      e = "bye"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "public references in local definitions are bound to the defining scope" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "Var" #= 1
        , "enclosingVar" #= "" #. "Var"
        , "" #. "nested" #= block_
          [ "" #. "Var" #= 2
          , "" #. "a" #= "enclosingVar"
          ] #. "a"
        ] #. "nested"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "definition errors in nested scopes are returned with errors in outer scopes" ~: let
      r :: Expr a => a
      r = block_
        [ "x" #= block_
          [ "" #. "a" #= 1
          , "" #. "a" #= 2
          ]
        , "" #. "x" #= "abc"
        ] #. "x"
      e = [OlappedSet ("" #. "a"), OlappedVis ("x")]
      in fails (assertEqual (banner r) e) (expr r)
  ]
  
 
paths
  :: (Expr a, Lit b, IsString b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test
paths expr = test
  [ "nested components can be accessed by paths" ~: let
      r :: Expr a => a
      r = block_ [
        "" #. "a" #= block_ [ "" #. "aa" #= 2 ]
        ] #. "a" #. "aa"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "nested components can be defined for paths" ~: let
      r :: Expr a => a
      r = block_ [ "" #. "a" #. "aa" #= 2 ] #. "a" #. "aa"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "public reference scopes to definition root when assigning path" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "f" #= "x"
        , "" #. "a" #. "f" #= "" #. "f"
        ] #. "a" #. "f"
      e = "x"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "public reference scopes to definition root when assigning to long path" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "f" #= 2
        , "" #. "a" #. "f" #. "g" #= "" #. "f"
        ] #. "a" #. "f" #. "g"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "components can access nested components via long paths" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "raba" #=
            "y1" #. "a" #. "ab" #. "aba"
        , "y1" #=
            block_ [ "" #. "a" #. "ab" #. "aba" #= 3 ]
        ] #. "raba"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "subpaths of path-defined nested components can be referenced" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #. "aa" #. "aaa" #= 2
        , "" #. "b" #= "" #. "a" #. "aa"
        ] #. "b" #. "aaa"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "private references bind to root scope when assigning path" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #. "f" #= "f" 
        , "f" #= "g"
        ] #. "a" #. "f"
      e = "g"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "can make private assignments using paths" ~: let
      r :: Expr a => a
      r = block_
        [ "Var" #. "field" #= 2
        , "" #. "x" #= "Var"
        ] #. "x" #. "field"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "assigning to a path overlapping with a defined value within same scope is forbidden" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "x" #= block_ [ "" #. "a" #= 1 ]
        , "" #. "x" #. "b" #= 2
        ]
      e = [OlappedSet ("" #. "x")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "can assign to disjoint paths with shared prefix within a scope" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "x" #. "a" #= 1
        , "" #. "x" #. "b" #= 2
        , "" #. "y" #= "" #. "x" #."a" #+ "" #. "x" #. "b"
        ] #. "y"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
          
  , "can assign to disjoint parts of a private definition" ~: let
      r :: Expr a => a
      r = block_
        [ "x" #. "y" #. "z" #= "hi" 
        , "x" #. "yy" #= "x" #. "y"
        , "" #. "ret" #= "x" #. "yy" #. "z"
        ] #. "ret"
      e = "hi"
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "assigning to paths where a leaf definition is overlapped is forbidden" ~: let
      r :: Expr a => a
      r = block_ 
        [ "x" #. "y" #. "z" #=
            block_ [ "" #. "x" #= "hi" ]
        , "x" #. "y" #=
            block_ [ "" #. "abc" #= "" #. "g" ]
        , "" #. "ret" #=
            "x" #. "yy" #. "z"
        ] #. "ret"
      e = [OlappedSet ("" #. "y")]
      in fails (assertEqual (banner r) e) (expr r)

  , "assigning to a path through a value from an outer scope makes a shadowed definition with the updated path" ~: let
      r :: Expr a => a
      r = block_
        [ "x" #= block_ [ "" #. "a" #= 1 ]
        , "y" #= block_
          [ "x" #. "b" #= 2
          , "" #. "return" #= "x"
          ] #. "return"
        , "" #. "call" #=
            "y" #. "a" #+ "y" #. "b"
        ] #. "call"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "original value is not affected by shadowing update in nested scope" ~: let
      r :: Expr a => a
      r = block_
        [ "x" #= block_
          [ "" #. "a" #= 2
          , "" #. "b" #= 1
          ]
        , "y" #= block_
          [ "x" #. "b" #= 2
          , "" #. "return" #= "x"
          ] #. "return"
        , "" #. "call" #=
            "x" #. "b" #+ "y" #. "b"
        ] #. "call"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
        
  ]

{-  
escape
  :: (Expr a, Lit b, Local b, Self b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test
escape expr = test
  [ "escaped component definitions scope to enclosing block" ~: let
      r :: Expr a => a
      r = block_
        [ "a" #= "str"
        , "" #. "b" #= block_
          [  "" #. "f" #= esc_ ("a") ]
        ] #. "b" #. "f"
      e = "str"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "sibling component definitions are not referable in escaped definitions" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= 1
        , "" #. "b" #= esc_ ("" #. "a")
        ] #. "b"
      e = "" #. "a"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "private aliases of sibling component definitions are not referable in escaped definitions" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "b" #= esc_ ("f")
        , "" #. "f" #= "g"
        ] #. "b"
      e = "f"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "public pun assigns outer declared public variable to local public field" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "b" #= 1
        , "" #. "x" #= block_ [ esc_ ("" #. "b") ] #. "b"
        ] #. "x"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "private pun assigns declared variable in private scope to local public field" ~: let
      r :: Expr a => a
      r = block_ [ esc_ ("x") ] #. "x"
      e = "x"
      in parses (expr r) >>= assertEqual (banner r) e
        
  ]
-}

extension
  :: (Expr a, Lit b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test
extension expr = test
  [ "extended components override original" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= 2
        , "" #. "b" #= "" #. "a"
        ] # block_ [ "" #. "a" #= 1 ] #. "b"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "override later of mutually-referencing 'default' definitions" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= "" #. "b"
        , "" #. "b" #= "" #. "a"
        ] # block_ [ "" #. "b" #= 2 ] #. "a"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "override earlier of mutually-referencing 'default' definitions" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= "" #. "b"
        , "" #. "b" #= "" #. "a"
        ] # block_ [ "" #. "a" #= 1 ] #. "b"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
       
  , "nested components of extension override nested components of original" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "a" #= block_ [ "" #. "aa" #= 0 ]
        , "" #. "b" #= "" #. "a" #. "aa"
        ] # block_ [ "" #. "a" #. "aa" #= 1 ] #. "b"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "self references can be used in extension" ~: let
      r :: Expr a => a
      r = block_
        [ "w1" #= block_ [ "" #. "a" #= 1 ]
        , "" #. "w2" #=
            "w1" # block_ [ "" #. "b" #= "" #. "a" ]
        , "" #. "ret" #=
            "" #. "w2" #. "b" #+ "" #. "w2" #. "a"
        ] #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "object fields alias not in scope for extensions" ~: let
      r :: Expr a => a
      r = block_
        [ "a" #= 2
        , "w1" #= block_ [ "" #. "a" #= 1 ]
        , "" #. "w2" #= "w1" # block_ [ "" #. "b" #= "a" ]
        ] #. "w2" #. "b"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "extension components of extended object can be accessed" ~: let
      r :: Expr a => a
      r = block_
        [ "" #. "w1" #= block_ [ "" #. "a" #= 1 ]
        , "" #. "w2" #= "" #. "w1" # block_ [ "" #. "b" #= 2 ]
        ] #. "w2" #. "b"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "extension private assignments do not shadow fields of original" ~: let
      r :: Expr a => a
      r = block_
        [ "original" #= block_
          [ "priv" #= 1
          , "" #. "privVal" #= "priv"
          ]
        , "new" #= "original" # block_ [ "priv" #= 2 ]
        , "" #. "call" #= "new" #. "privVal"
        ] #. "call"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "extension can reference original version lexically" ~: let
      r :: Expr a => a
      r = block_
        [ "y" #= block_ [ "" #. "a" #= 1 ]
        , "" #. "call" #= "y" # block_ 
          [ "" #. "a" #= "y" #. "a" ] #. "a"
        ] #. "call"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
 
  ]


patterns
  :: (Expr a, Lit b, Eq b, Show b)
  => (a -> Either [DefnError Ident] b) -> Test
patterns expr = test
  [ "decomposition block assigns components of a value" ~: let
      r :: Expr a => a
      r = block_
        [ "obj" #= block_
          [ "" #. "a" #= 2
          , "" #. "b" #= 3
          ]
        , block_
          [ "" #. "a" #= "da"
          , "" #. "b" #= "" #. "db"
          ] #= "obj"
        , "" #. "ret" #= "da" #- "" #. "db"
        ] #. "ret"
      e = fromInteger (-1)
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "decomposed values are assigned to corresponding leaf paths" ~: let
      r :: Expr a => a
      r = block_
        [ "obj" #= block_
          [ "" #. "fp" #= 1
          , "" #. "fz" #= 3
          , "" #. "fc" #= quote_ "xy"
          ]
        , block_
          [ "" #. "fp" #= "" #. "gp"
          , "" #. "fz" #= "" #. "gz"
          , "" #. "fc" #= "" #. "gc"
          ] #= "obj"
        ] #. "gc"
      e = quote_ "xy"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "decomposed values assignments are independent of declaration order" ~: let
      r :: Expr a => a
      r = block_
        [ "obj" #= block_
          [ "" #. "fc" #= quote_ "xy"
          , "" #. "fz" #= 3
          , "" #. "fp" #= 1
          ]
        , block_
          [ "" #. "fc" #= "" #. "gc"
          , "" #. "fz" #= "" #. "gz"
          , "" #. "fp" #= "" #. "gp"
          ] #= "obj"
        ] #. "gc"
      e = quote_ "xy"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "destructuring a component twice in the same decomposition block is forbidden" ~: let
      r :: Expr a => a
      r = block_ [
        block_
          [ "" #. "a" #= "pa"
          , "" #. "a" #= "" #. "pb"
          ] #= "p"
        ] #. "pb"
      e = [OlappedMatch "a"]
      in fails (assertEqual (banner r) e) (expr r)

  , "components not deconstructed in a decomposition block can be assigned to a trailing path" ~: let
      r :: Expr a => a
      r = block_
        [ "obj" #= block_
          [ "" #. "a" #= 2
          , "" #. "b" #= 3
          ]
        , "" #. "d" # block_ [ "" #. "a" #= "x" ] #= "obj"
        , "" #. "ret" #= "" #. "d" #. "b"
        ] #. "ret"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "deconstructed components are assigned to corresponding paths when a trailing path is used" ~: let
      r :: Expr a => a
      r = block_
        [ "obj" #= block_
          [ "" #. "a" #= 2
          , "" #. "b" #= 3
          ]
        , "" #. "d" # block_ [ "" #. "a" #= "x" ] #= "obj"
        , "" #. "ret" #= "x"
        ] #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "can assign an empty block to a trailing path if all components are deconstructed" ~: let
      r :: Expr a => a
      r = block_
        [ "obj" #= block_ [ "" #. "a" #= 2 ]
        , "x" # block_ [ "" #. "a" #= "y" ] #= "obj"
        , "" #. "ret" #= "y"
        ] #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
          
  , "paths can be used to deconstruct nested components" ~: let
      r :: Expr a => a
      r = block_ 
        [ "get" #= block_ [ "" #. "f" #. "g" #= 4 ]
        , block_ [ "" #. "f" #. "g" #= "set" ] #= "get"
        , "" #. "ret" #= "set"
        ] #. "ret"
      e = 4
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "multiple paths to disjoint nested components can be deconstructed" ~: let
      r :: Expr a => a
      r = block_
        [ "a" #= block_
          [ "" #. "x" #= block_
            [ "" #. "y1" #= 2
            , "" #. "y2" #= 3
            ]
          ]
        , block_
          [ "" #. "x" #. "y1" #= "a1"
          , "" #. "x" #. "y2" #= "a2"
          ] #= "a"
        , "" #. "ret" #= "a1" #- "a2"
        ] #. "ret"
      e = fromInteger (-1)
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "multiple disjoint long paths can be deconstructed" ~: let
      r :: Expr a => a
      r = block_
        [ block_
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #. "z" #. "yy" #= "b2"
          ] #= "a"
        , "a" #= block_
          [ "" #. "x" #. "z" #. "y" #= "hello"
          , "" #. "x" #. "z" #. "yy" #= 34
          ]
        , "" #. "ret" #= "b2"
        ] #. "ret"
      e = 34
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "destructured paths must not be duplicates" ~: let
      r :: Expr a => a
      r = block_
        [ block_
          [ "" #. "x" #. "z" #= "b1"
          , "" #. "x" #. "z" #= "b2"
          ] #= "a"
        , "a" #= block_
          [ "" #. "x" #. "z" #= "hello" ]
        , "" #. "ret" #= "b2"
        ] #. "ret"
      e = [OlappedMatch "z"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured long paths must not be duplicates" ~: let
      r :: Expr a => a
      r = block_
        [ block_
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #. "z" #. "y" #= "b2"
          ] #= "a"
        , "a" #= block_
          [ "" #. "x" #. "z" #. "y" #= "hello" ]
        , "" #. "ret" #= "b2"
        ] #. "ret"
      e = [OlappedMatch "y"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured paths must be disjoint from other destructured components" ~: let
      r :: Expr a => a
      r = block_
        [ block_
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #= "b2"
          ] #= "a"
        , "a" #= block_
          [ "" #. "x" #. "z" #. "y" #= "hello" ]
        , "" #. "ret" #= "b2" #. "z" #. "y"
        ] #. "ret"
      e = [OlappedMatch "x"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured paths must be disjoint from other destructured paths" ~: let
      r :: Expr a => a
      r = block_
        [ block_
          [ "" #. "x" #. "z" #= "b2"
          , "" #. "x" #. "z" #. "y" #= "b1"
          ] #= "a"
        , "a" #= block_
          [ "" #. "x" #. "z" #= block_
            [ "" #. "y" #= "hello" ]
          ]
        , "" #. "ret" #= "b2" #. "y"
        ] #. "ret"
      e = [OlappedMatch "z"]
      in fails (assertEqual (banner r) e) (expr r)
      
      
  , "destructured paths must be disjoint from other destructured components and paths" ~: let
      r :: Expr a => a
      r = block_
        [ block_
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #= "c1"
          , "" #. "x" #. "z" #= "b2"
          ] #= "a"
        , "a" #= block_
          [ "" #. "x" #. "z" #. "y" #= "hello" ]
        , "" #. "ret" #= "b2" #. "y"
        ] #. "ret"
      e = [OlappedMatch "x", OlappedMatch "z"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "a public name pun in a decomposition block assigns a component to the corresponding public name" ~: let
      r :: Expr a => a
      r = block_ 
        [ block_ [ "" #. "a" ] #= "o"
        , "o" #= block_ [ "" #. "a" #= 1 ]
        ] #. "a"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "a private name pun in a decomposition block assigns a component to the corresponding private name" ~: let
      r :: Expr a => a
      r = block_ 
        [ block_ [ "a" ] #= "o"
        , "o" #= block_ [ "" #. "a" #= 2 ]
        , "" #. "ret" #= "a"
        ] #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "a private path pun can be used to destructure a nested component to the corresponding local path" ~: let
      r :: Expr a => a
      r = block_
        [ block_ [ "a" #. "f" #. "g" ] #= block_
          [ "" #. "a" #. "f" #. "g" #= 4 ]
        , "" #. "ret" #= "a"
        ] #. "ret" #. "f" #. "g"
      e = 4
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "patterns can be nested in decomposition blocks" ~: let
      r :: Expr a => a
      r = block_
        [ "y1" #= block_
          [ "" #. "a" #= block_
            [ "" #. "aa" #= 3
            , "" #. "ab" #= block_ [ "" #. "aba" #= 4 ]
            ]
          ]
        , block_
          [ "" #. "a" #= block_
            [ "" #. "aa" #= "" #. "da"
            , "" #. "ab" #= block_
              [ "" #. "aba" #= "" #. "daba" ]
            ]
          ] #= "y1"
        , "" #. "raba" #= "y1" #. "a" #. "ab" #. "aba"
        , "" #. "ret" #= "" #. "raba" #- "" #. "daba"
        ] #. "ret"
      e = 0
      in parses (expr r) >>= assertEqual (banner r) e
      
  ]
