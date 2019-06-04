{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies, FlexibleContexts #-}
module Lang.Eval (tests) where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( CanonExpr, Self, IDENTIFIER, unself
  , toDefinition, showDefinition
  )
import Goat.Lang.Error
  ( DefnError(..), displayDefnError, displayErrorList )
import Test.HUnit
  
banner
 :: CanonExpr (Either Self IDENTIFIER) -> String
banner r
  = "For "
 ++ showDefinition (toDefinition (unself r)) ","

parses :: Either [DefnError] a -> IO a
parses
  = either 
      (fail . displayErrorList displayDefnError)
      return

fails
 :: Show a
 => ([DefnError] -> Assertion)
 -> Either [DefnError] a -> Assertion
fails f
  = either f
      (fail . showString "Unexpected: " . show)

tests
 :: (Definition_ a, Eq b, Show b)
 => (a -> Either [DefnError] b) -> Test
tests expr
  = TestList
  [ "operators" ~: operators expr
  , "blocks" ~: blocks expr
  , "scope" ~: scope expr
  , "paths" ~: paths expr
  --, "escape" ~: escape expr
  , "extension" ~: extension expr
  {-, "patterns" ~: patterns expr
  -}
  ]

operators
 :: ( NumLiteral_ a, TextLiteral_ a, Operator_ a
    , Eq b, Show b
    )
 => (a -> Either [DefnError] b) -> Test
operators expr
  = TestList
  [ "add"
     ~: let
        r :: (NumLiteral_ a, Operator_ a) => a
        r = (1 #+ 1)
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
        
  , "subtract"
     ~: let
        r :: (NumLiteral_ a, Operator_ a) => a
        r = (1 #- 2)
        e = fromInteger (-1)
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "mixed"
     ~: let
        r :: (NumLiteral_ a, Operator_ a) => a
        r = 1 #+ 1 #* 2 #- 2
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
        
  , "comparisons"
     ~: let
        r :: (NumLiteral_ a, Operator_ a) => a
        r = 3 #> 2
        e = 2 #<= 3
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
        
  , "equality"
     ~: let
        r :: (NumLiteral_ a, Operator_ a) => a
        r = 2 #!= 2
        e = not_ (2 #== 2)
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  ]
      
blocks
  :: (Definition_ a, Eq b, Show b)
  => (a -> Either [DefnError] b) -> Test      
blocks expr
  = TestList 
  [ "publicly declared component can be accessed"
     ~: let
        r :: Definition_ a => a
        r = [ "" #. "pub" #= 1 ] #. "pub"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
     
  , "locally declared component is not accesssible"
     ~: let
        r :: Definition_ a => a
        r = [ "priv" #= 1 ] #. "priv"
        in
        parses (expr r)
         >> assertFailure "##todo type error"
     
  , "values with multiple declared components return the corresponding value when a component is accessed"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #= 1,
          "" #. "b" #= 2,
          "" #. "c" #= quote_ "xy"
          ] #. "c"
        e = quote_ "xy"
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "components values are independent of declaration order"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "c" #= quote_ "xy",
          "" #. "a" #= 1,
          "" #. "b" #= 2
          ] #. "c"
        e = quote_ "xy"
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "component definition can reference previous private assignment in same scope"
    ~: let
        r :: Definition_ a => a
        r = [
          "priv" #= 1,
          "" #. "pub" #= "priv"
          ] #. "pub"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "component definition can reference later private assignment in same scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "pub" #= "priv",
          "priv" #= 1
          ] #. "pub"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "component can reference earlier public assignment from same scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "b" #= 2,
          "" #. "a" #= "" #. "b"
          ] #. "a"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "component can reference to later public assignment from same scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #= "" #. "b",
          "" #. "b" #= 2
          ] #. "a"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "public definition can be reference via a private alias"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #= 1,
          "" #. "b" #= "a"
          ] #. "b"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "component can transitively reference a public assignment via a privately declared reference"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "public" #= 1,
          "notPublic" #= "" #. "public",
          "" #. "x" #= "notPublic"
          ] #. "x"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "component can reference an unbound variable"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #= 2,
          "" #. "b" #= quote_ "c"
          ] #. "b"
        e = quote_ "c"
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "type error when transitively accessing an undeclared public field"
     ~: let
        r :: Definition_ a => a
        r = [ "" #. "b" #= "" #. "a" ] #. "b"
        in
        parses (expr r)
         >> assertFailure "##todo type error"
  
  , "component access does not execute unrelated components"
     ~: let
        r :: Definition_ a => a
        r = [
          "selfRef" #= "selfRef",
          "" #. "x" #= 2,
          "" #. "loop" #= "selfRef"
          ] #. "x"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "cannot assign private variable twice"
     ~: let
        r :: Definition_ a => a
        r = [
          "a" #= 1,
          "a" #= "hello"
          ]
        e = [OlappedSet ("a")]
        in
        fails (assertEqual (banner r) e) (expr r)
      
  , "cannot assign public variable twice"
     ~: let
        r :: Definition_ a => a
        r = [ "" #. "x" #= 1
            , "" #. "x" #= "a"
            ]
        e = [OlappedSet ("x")]
        in
        fails (assertEqual (banner r) e) (expr r)
      
  , "cannot assign same public and private variable" 
     ~: let
        r :: Definition_ a => a
        r = [
          "a" #= "first",
          "" #. "a" #= "second"
          ]
        e = [OlappedSet ("a")]
        in
        fails (assertEqual (banner r) e) (expr r)
    
  , "block component definitions be self-referential"
     ~: let
        r :: Definition_ a => a
        r = [
          "y" #= [
            "" #. "a" #= "y" #. "b",
            "" #. "b" #= 1
            ],
          "" #. "call" #= "y" #. "a"
          ] #. "call"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  ]

scope
  :: (Definition_ a, Eq b, Show b)
  => (a -> Either [DefnError] b) -> Test
scope expr
  = TestList  
  [ "component can access public components of nested blocks"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "return" #= [
            "" #. "return" #= quote_ "str"
            ] #. "return"
          ] #. "return"
        e = quote_ "str"
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "components can access nested components via reference to local assignment in same scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "object" #= [ "" #. "b" #= 1 ],
          "" #. "c" #= "object" #. "b"
          ] #. "c"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "nested block definitions can reference outer public definitions via private alias"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #= 1,
          "object" #= [ "" #. "b" #= "a" ],
          "" #. "c" #= "object" #. "b"
          ] #. "c"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "nested block private assignments shadows private assignment of outer scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "outer" #= 1,
          "" #. "inner" #= [
            "outer" #= 2,
            "" #. "shadow" #= "outer"
            ] #. "shadow"
          ] #. "inner"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "nested block private assignment shadows private alias for outer public assignment"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "outer" #= quote_ "hello",
          "" #. "inner" #= [
            "" #. "shadow" #= "outer",
            "outer" #= quote_ "bye"
            ] #. "shadow"
          ] #. "inner"
        e = quote_ "bye"
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "public references in local definitions are bound to the defining scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "Var" #= 1,
          "enclosingVar" #= "" #. "Var",
          "" #. "nested" #= [
            "" #. "Var" #= 2,
            "" #. "a" #= "enclosingVar"
            ] #. "a"
          ] #. "nested"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "definition errors in nested scopes are returned with errors in outer scopes"
     ~: let
        r :: Definition_ a => a
        r = [
          "x" #= [
            "" #. "a" #= 1,
            "" #. "a" #= 2
            ],
          "" #. "x" #= "abc"
          ] #. "x"
        e = [OlappedSet ("a"), OlappedSet ("x")]
        in
        fails (assertEqual (banner r) e) (expr r)

  ]

paths
 :: (Definition_ a, Eq b, Show b)
 => (a -> Either [DefnError] b) -> Test
paths expr
  = TestList
  [ "nested components can be accessed by paths"
     ~: let
        r :: Definition_ a => a
        r = [ 
          "" #. "a" #= [ "" #. "aa" #= 2 ]
          ] #. "a" #. "aa"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "nested components can be defined for paths"
     ~: let
        r :: Definition_ a => a
        r = [ "" #. "a" #. "aa" #= 2 ] #. "a" #. "aa"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "public reference scopes to definition root when assigning path"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "f" #= quote_ "x",
          "" #. "a" #. "f" #= "" #. "f"
          ] #. "a" #. "f"
        e = quote_ "x"
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "public reference scopes to definition root when assigning to long path"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "" #. "f" #= 2
          , "" #. "a" #. "f" #. "g" #= "" #. "f"
          ] #. "a" #. "f" #. "g"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "components can access nested components via long paths"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "raba" #=
              "y1" #. "a" #. "ab" #. "aba",
          "y1" #= [
            "" #. "a" #. "ab" #. "aba" #= 3
            ]
          ] #. "raba"
        e = 3
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "subpaths of path-defined nested components can be referenced"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #. "aa" #. "aaa" #= 2,
          "" #. "b" #= "" #. "a" #. "aa"
          ] #. "b" #. "aaa"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "private references bind to root scope when assigning path"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #. "f" #= "f",
          "f" #= quote_ "g"
          ] #. "a" #. "f"
        e = quote_ "g"
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "can make private assignments using paths"
     ~: let
        r :: Definition_ a => a
        r = [
          "Var" #. "field" #= 2,
          "" #. "x" #= "Var"
          ] #. "x" #. "field"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "assigning to a path overlapping with a defined value within same scope is forbidden"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "x" #= [ "" #. "a" #= 1 ],
          "" #. "x" #. "b" #= 2
          ]
        e = [OlappedSet ("x")]
        in
        fails (assertEqual (banner r) e) (expr r)
      
  , "can assign to disjoint paths with shared prefix within a scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "x" #. "a" #= 1,
          "" #. "x" #. "b" #= 2,
          "" #. "y" #=
            "" #. "x" #."a" #+ "" #. "x" #. "b"
          ] #. "y"
        e = 3
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "can assign to disjoint parts of a private definition"
     ~: let
        r :: Definition_ a => a
        r = [
          "x" #. "y" #. "z" #= quote_ "hi",
          "x" #. "yy" #= "x" #. "y",
          "" #. "ret" #= "x" #. "yy" #. "z"
          ] #. "ret"
        e = quote_ "hi"
        in 
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "assigning to paths where a leaf definition is overlapped is forbidden"
     ~: let
        r :: Definition_ a => a
        r = [
          "x" #. "y" #. "z" #= [
            "" #. "x" #= "hi"
            ],
          "x" #. "y" #= [
            "" #. "abc" #= "" #. "g" ],
          "" #. "ret" #=
              "x" #. "yy" #. "z"
          ] #. "ret"
        e = [OlappedSet ("y")]
        in
        fails (assertEqual (banner r) e) (expr r)

  , "assigning to a path through a value from an outer scope makes a shadowed definition with the updated path"
     ~: let
        r :: Definition_ a => a
        r = [
          "x" #= [ "" #. "a" #= 1 ],
          "y" #= [
            "x" #. "b" #= 2,
            "" #. "return" #= "x"
            ] #. "return",
          "" #. "call" #=
              "y" #. "a" #+ "y" #. "b"
          ] #. "call"
        e = 3
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "original value is not affected by shadowing update in nested scope"
     ~: let
        r :: Definition_ a => a
        r = [
          "x" #= [
            "" #. "a" #= 2,
            "" #. "b" #= 1
            ],
          "y" #= [
            "x" #. "b" #= 2,
            "" #. "return" #= "x"
            ] #. "return",
          "" #. "call" #=
              "x" #. "b" #+ "y" #. "b"
          ] #. "call"
        e = 3
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  ]

{-  
escape
  :: (Expr a, Lit b, Local b, Self b, Eq b, Show b)
  => (a -> Either [DefnError] b) -> Test
escape expr = TestList
  [ "escaped component definitions scope to enclosing block" ~: let
      r :: Definition_ a => a
      r = 
        [ "a" #= "str"
        , "" #. "b" #= 
          [  "" #. "f" #= esc_ ("a") ]
        ] #. "b" #. "f"
      e = "str"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "sibling component definitions are not referable in escaped definitions" ~: let
      r :: Definition_ a => a
      r = 
        [ "" #. "a" #= 1
        , "" #. "b" #= esc_ ("" #. "a")
        ] #. "b"
      e = "" #. "a"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "private aliases of sibling component definitions are not referable in escaped definitions" ~: let
      r :: Definition_ a => a
      r = 
        [ "" #. "b" #= esc_ ("f")
        , "" #. "f" #= "g"
        ] #. "b"
      e = "f"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "public pun assigns outer declared public variable to local public field" ~: let
      r :: Definition_ a => a
      r = 
        [ "" #. "b" #= 1
        , "" #. "x" #= [ esc_ ("" #. "b") ] #. "b"
        ] #. "x"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "private pun assigns declared variable in private scope to local public field" ~: let
      r :: Definition_ a => a
      r = [ esc_ ("x") ] #. "x"
      e = "x"
      in parses (expr r) >>= assertEqual (banner r) e
        
  ]
-}

extension
 :: (Definition_ a, Eq b, Show b)
 => (a -> Either [DefnError] b) -> Test
extension expr
  = TestList
  [ "extended components replace original"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #= 2
          ] # [ "" #. "a" #= 1 ] #. "a"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
     
  , "extended component definitions override original"
     ~: let
        r :: Definition_ a => a
        r = [
          "" #. "a" #= 2,
          "" #. "b" #= "" #. "a"
          ] # [ "" #. "a" #= 1 ] #. "b"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "override later of mutually-referencing 'default' definitions"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "" #. "a" #= "" #. "b"
          , "" #. "b" #= "" #. "a"
          ] # [ "" #. "b" #= 2 ] #. "a"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "override earlier of mutually-referencing 'default' definitions"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "" #. "a" #= "" #. "b"
          , "" #. "b" #= "" #. "a"
          ] # [ "" #. "a" #= 1 ] #. "b"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "nested components of extension override nested components of original"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "" #. "a" #= [ "" #. "aa" #= 0 ]
          , "" #. "b" #= "" #. "a" #. "aa"
          ] # [ "" #. "a" #. "aa" #= 1 ] #. "b"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
        
  , "self references can be used in extension"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "w1" #= [ "" #. "a" #= 1 ]
          , "" #. "w2" #=
              "w1" # [ "" #. "b" #= "" #. "a" ]
          , "" #. "ret" #=
              "" #. "w2" #. "b" #+ "" #. "w2" #. "a"
          ] #. "ret"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "object fields alias not in scope for extensions"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "a" #= 2
          , "w1" #= [ "" #. "a" #= 1 ]
          , "" #. "w2" #= "w1" # [ "" #. "b" #= "a" ]
          ] #. "w2" #. "b"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "extension components of extended object can be accessed"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "" #. "w1" #= [ "" #. "a" #= 1 ]
          , "" #. "w2" #= "" #. "w1" # [ "" #. "b" #= 2 ]
          ] #. "w2" #. "b"
        e = 2
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "extension private assignments do not shadow fields of original"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "original" #= 
            [ "priv" #= 1
            , "" #. "privVal" #= "priv"
            ]
          , "new" #= "original" # [ "priv" #= 2 ]
          , "" #. "call" #= "new" #. "privVal"
          ] #. "call"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  , "extension can reference original version lexically"
     ~: let
        r :: Definition_ a => a
        r = 
          [ "y" #= [ "" #. "a" #= 1 ]
          , "" #. "call" #= "y" #  
            [ "" #. "a" #= "y" #. "a" ] #. "a"
          ] #. "call"
        e = 1
        in
        do
          e <- parses (expr e)
          a <- parses (expr r)
          assertEqual (banner r) e a
  
  ]


patterns
 :: (Definition_ a, Eq b, Show b)
 => (a -> Either [DefnError] b) -> Test
patterns expr = TestList
  [ "decomposition block assigns components of a value" ~: let
      r :: Definition_ a => a
      r = 
        [ "obj" #= 
          [ "" #. "a" #= 2
          , "" #. "b" #= 3
          ]
        , 
          [ "" #. "a" #= "da"
          , "" #. "b" #= "" #. "db"
          ] #= "obj"
        , "" #. "ret" #= "da" #- "" #. "db"
        ] #. "ret"
      e = fromInteger (-1)
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "decomposed values are assigned to corresponding leaf paths" ~: let
      r :: Definition_ a => a
      r = 
        [ "obj" #= 
          [ "" #. "fp" #= 1
          , "" #. "fz" #= 3
          , "" #. "fc" #= quote_ "xy"
          ]
        , 
          [ "" #. "fp" #= "" #. "gp"
          , "" #. "fz" #= "" #. "gz"
          , "" #. "fc" #= "" #. "gc"
          ] #= "obj"
        ] #. "gc"
      e = quote_ "xy"
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "decomposed values assignments are independent of declaration order" ~: let
      r :: Definition_ a => a
      r = 
        [ "obj" #= 
          [ "" #. "fc" #= quote_ "xy"
          , "" #. "fz" #= 3
          , "" #. "fp" #= 1
          ]
        , 
          [ "" #. "fc" #= "" #. "gc"
          , "" #. "fz" #= "" #. "gz"
          , "" #. "fp" #= "" #. "gp"
          ] #= "obj"
        ] #. "gc"
      e = quote_ "xy"
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "destructuring a component twice in the same decomposition block is forbidden" ~: let
      r :: Definition_ a => a
      r = [
        
          [ "" #. "a" #= "pa"
          , "" #. "a" #= "" #. "pb"
          ] #= "p"
        ] #. "pb"
      e = [OlappedMatch "a"]
      in fails (assertEqual (banner r) e) (expr r)

  , "components not deconstructed in a decomposition block can be assigned to a trailing path" ~: let
      r :: Definition_ a => a
      r = 
        [ "obj" #= 
          [ "" #. "a" #= 2
          , "" #. "b" #= 3
          ]
        , "" #. "d" # [ "" #. "a" #= "x" ] #= "obj"
        , "" #. "ret" #= "" #. "d" #. "b"
        ] #. "ret"
      e = 3
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "deconstructed components are assigned to corresponding paths when a trailing path is used" ~: let
      r :: Definition_ a => a
      r = 
        [ "obj" #= 
          [ "" #. "a" #= 2
          , "" #. "b" #= 3
          ]
        , "" #. "d" # [ "" #. "a" #= "x" ] #= "obj"
        , "" #. "ret" #= "x"
        ] #. "ret"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "can assign an empty block to a trailing path if all components are deconstructed" ~: let
      r :: Definition_ a => a
      r = 
        [ "obj" #= [ "" #. "a" #= 2 ]
        , "x" # [ "" #. "a" #= "y" ] #= "obj"
        , "" #. "ret" #= "y"
        ] #. "ret"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
          
  , "paths can be used to deconstruct nested components" ~: let
      r :: Definition_ a => a
      r =  
        [ "get" #= [ "" #. "f" #. "g" #= 4 ]
        , [ "" #. "f" #. "g" #= "set" ] #= "get"
        , "" #. "ret" #= "set"
        ] #. "ret"
      e = 4
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "multiple paths to disjoint nested components can be deconstructed" ~: let
      r :: Definition_ a => a
      r = 
        [ "a" #= 
          [ "" #. "x" #= 
            [ "" #. "y1" #= 2
            , "" #. "y2" #= 3
            ]
          ]
        , 
          [ "" #. "x" #. "y1" #= "a1"
          , "" #. "x" #. "y2" #= "a2"
          ] #= "a"
        , "" #. "ret" #= "a1" #- "a2"
        ] #. "ret"
      e = fromInteger (-1)
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "multiple disjoint long paths can be deconstructed" ~: let
      r :: Definition_ a => a
      r = 
        [ 
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #. "z" #. "yy" #= "b2"
          ] #= "a"
        , "a" #= 
          [ "" #. "x" #. "z" #. "y" #= "hello"
          , "" #. "x" #. "z" #. "yy" #= 34
          ]
        , "" #. "ret" #= "b2"
        ] #. "ret"
      e = 34
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "destructured paths must not be duplicates" ~: let
      r :: Definition_ a => a
      r = 
        [ 
          [ "" #. "x" #. "z" #= "b1"
          , "" #. "x" #. "z" #= "b2"
          ] #= "a"
        , "a" #= 
          [ "" #. "x" #. "z" #= "hello" ]
        , "" #. "ret" #= "b2"
        ] #. "ret"
      e = [OlappedMatch "z"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured long paths must not be duplicates" ~: let
      r :: Definition_ a => a
      r = 
        [ 
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #. "z" #. "y" #= "b2"
          ] #= "a"
        , "a" #= 
          [ "" #. "x" #. "z" #. "y" #= "hello" ]
        , "" #. "ret" #= "b2"
        ] #. "ret"
      e = [OlappedMatch "y"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured paths must be disjoint from other destructured components" ~: let
      r :: Definition_ a => a
      r = 
        [ 
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #= "b2"
          ] #= "a"
        , "a" #= 
          [ "" #. "x" #. "z" #. "y" #= "hello" ]
        , "" #. "ret" #= "b2" #. "z" #. "y"
        ] #. "ret"
      e = [OlappedMatch "x"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured paths must be disjoint from other destructured paths" ~: let
      r :: Definition_ a => a
      r = 
        [ 
          [ "" #. "x" #. "z" #= "b2"
          , "" #. "x" #. "z" #. "y" #= "b1"
          ] #= "a"
        , "a" #= 
          [ "" #. "x" #. "z" #= 
            [ "" #. "y" #= "hello" ]
          ]
        , "" #. "ret" #= "b2" #. "y"
        ] #. "ret"
      e = [OlappedMatch "z"]
      in fails (assertEqual (banner r) e) (expr r)
      
      
  , "destructured paths must be disjoint from other destructured components and paths" ~: let
      r :: Definition_ a => a
      r = 
        [ 
          [ "" #. "x" #. "z" #. "y" #= "b1"
          , "" #. "x" #= "c1"
          , "" #. "x" #. "z" #= "b2"
          ] #= "a"
        , "a" #= 
          [ "" #. "x" #. "z" #. "y" #= "hello" ]
        , "" #. "ret" #= "b2" #. "y"
        ] #. "ret"
      e = [OlappedMatch "x", OlappedMatch "z"]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "a public name pun in a decomposition block assigns a component to the corresponding public name" ~: let
      r :: Definition_ a => a
      r =  
        [ [ "" #. "a" ] #= "o"
        , "o" #= [ "" #. "a" #= 1 ]
        ] #. "a"
      e = 1
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "a private name pun in a decomposition block assigns a component to the corresponding private name" ~: let
      r :: Definition_ a => a
      r =  
        [ [ "a" ] #= "o"
        , "o" #= [ "" #. "a" #= 2 ]
        , "" #. "ret" #= "a"
        ] #. "ret"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
    
  , "a private path pun can be used to destructure a nested component to the corresponding local path" ~: let
      r :: Definition_ a => a
      r = 
        [ [ "a" #. "f" #. "g" ] #= 
          [ "" #. "a" #. "f" #. "g" #= 4 ]
        , "" #. "ret" #= "a"
        ] #. "ret" #. "f" #. "g"
      e = 4
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
    
  , "patterns can be nested in decomposition blocks" ~: let
      r :: Definition_ a => a
      r = 
        [ "y1" #= 
          [ "" #. "a" #= 
            [ "" #. "aa" #= 3
            , "" #. "ab" #= [ "" #. "aba" #= 4 ]
            ]
          ]
        , 
          [ "" #. "a" #= 
            [ "" #. "aa" #= "" #. "da"
            , "" #. "ab" #= 
              [ "" #. "aba" #= "" #. "daba" ]
            ]
          ] #= "y1"
        , "" #. "raba" #= "y1" #. "a" #. "ab" #. "aba"
        , "" #. "ret" #= "" #. "raba" #- "" #. "daba"
        ] #. "ret"
      e = 0
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  ]
