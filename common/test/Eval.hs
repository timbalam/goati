{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Eval
  ( tests
  )
  where

--import My.Eval (simplify, K)
--import My.Types.Repr (Repr(..), Prim(..), eval)
import My.Types.Syntax.Class
import My.Syntax.Parser (Printer, showP)
import qualified My.Types.Parser as P
import My.Syntax.Interpreter (DefnError(..), MyException(..))
import Data.Void (Void)
import Control.Exception (ioError, displayException)
import Test.HUnit
  
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


parses :: Either [DefnError] a -> IO a
parses = either 
  (ioError . userError . displayException
    . MyExceptions :: [DefnError] -> IO a)
  return
  
  
fails :: Show a => ([DefnError] -> Assertion) -> Either [DefnError] a -> Assertion
fails f = either f (ioError . userError . shows "Unexpected: " . show)


tests
  :: (Expr a, Lit b, Self b, Local b, Eq b, Show b) => (a -> Either [DefnError] b) -> Test
tests expr = test
  [ "literals" ~: literals expr
  , "blocks" ~: blocks expr
  , "scope" ~: scope expr
  , "paths" ~: paths expr
  , "tuple" ~: tuple expr
  , "extension" ~: extension expr
  , "patterns" ~: patterns expr
  ]

literals
  :: (Lit a, Lit b, Eq b, Show b) => (a -> Either [DefnError] b) -> Test
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
  :: (Expr a, Lit b, Local b, Self b, Eq b, Show b)
  => (a -> Either [DefnError] b) -> Test      
blocks expr = test 
  [ "publicly declared component can be accessed" ~: let
      r :: Expr a => a
      r = block_ ( self_ "pub" #= 1 ) #. "pub"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
     
  , "locally declared component is not accesssible ##todo type error" ~: let
      r :: Expr a => a
      r = block_ ( local_ "priv" #= 1 ) #. "priv"
      in parses (expr r) >>= assertFailure . show
      
  , "values with multiple declared components return the corresponding value when a component is accessed" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "a" #= 1
        #: self_ "b" #= 2
        #: self_ "c" #= "xy"
        ) #. "c"
      e = "xy"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "components values are independent of declaration order" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "c" #= "xy"
        #: self_ "a" #= 1
        #: self_ "b" #= 2
        ) #. "c"
      e = "xy"
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "component definition can reference previous private assignment in same scope" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "priv" #= 1
        #: self_ "pub" #= local_ "priv"
        ) #. "pub"
      e = 1
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
      
  , "component definition can reference later private assignment in same scope" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "pub" #= local_ "priv" #:
        local_ "priv" #= 1
        ) #. "pub"
      e = 1
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "component can reference earlier public assignment from same scope" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "b" #= 2 #:
        self_ "a" #= self_ "b"
        ) #. "a"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "component can reference to later public assignment from same scope" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "a" #= self_ "b" #:
        self_ "b" #= 2
        ) #. "a"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "public definition can be reference via a private alias" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "a" #= 1 #:
        self_ "b" #= local_ "a"
        ) #. "b"
      e = 1
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "component can transitively reference a public assignment via a privately declared reference" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "public" #= 1
        #: local_ "notPublic" #= self_ "public"
        #: self_ "x" #= local_ "notPublic"
        ) #. "x"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "component can reference an unbound variable" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "a" #= 2
        #: self_ "b" #= local_ "c"
        ) #. "b"
      e = local_ "c"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "type error when transitively accessing an undeclared public field ##todo type error" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "b" #= self_ "a"
        ) #. "b"
      in parses (expr r) >>= assertFailure . show
  
  , "component access does not execute unrelated components" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "selfRef" #= local_ "selfRef"
        #: self_ "x" #= 2
        #: self_ "loop" #= local_ "selfRef"
        ) #. "x"
      e = 2
      in parses (expr e) >>= \ e ->
        parses (expr r) >>= assertEqual (banner r) e
        
  , "cannot assign private variable twice" ~: let
      r :: Expr a => a
      r = block_ ( local_ "a" #= 1 #: local_ "a" #= "hello" )
      e = [OlappedSet (local_ "a")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "cannot assign public variable twice" ~: let
      r :: Expr a => a
      r = block_ ( self_ "x" #= 1 #: self_ "x" #= local_ "a" )
      e = [OlappedSet (self_ "x")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "cannot assign same public and private variable" ~: let
      r :: Expr a => a
      r = block_ ( local_ "a" #= "first" #: self_ "a" #= "second" )
      e = [OlappedVis (local_ "a")]
      in fails (assertEqual (banner r) e) (expr r)
      
      
  , "cannot assign variable twice in tup Block" ~: let
      r :: Expr a => a
      r = tup_ ( self_ "ab" #= local_ "ab" #: self_ "ab" #= 2 )
      e = [OlappedSet (self_ "ab")]
      in fails (assertEqual (banner r) e) (expr r)
    
  , "block component definitions be self-referential" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "y" #= block_
          ( self_ "a" #= local_ "y" #. "b"
          #: self_ "b" #= 1
          )
        #: self_ "call" #= local_ "y" #. "a"
        ) #. "call"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
  ]

scope :: (Expr a, Lit b, Local b, Self b, Eq b, Show b) => (a -> Either [DefnError] b) -> Test
scope expr = test  
  [ "component can access public components of nested blocks" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "return" #=
            block_ ( self_ "return" #= "str" ) #. "return"
        ) #. "return"
      e = "str"
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "components can access nested components via reference to local assignment in same scope" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "object" #= block_ ( self_ "b" #= 1 )
        #: self_ "c" #= local_ "object" #. "b"
        ) #. "c"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "nested block definitions can reference outer public definitions via private alias" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "a" #= 1
        #: local_ "object" #= block_ ( self_ "b" #= local_ "a" )
        #: self_ "c" #= local_ "object" #. "b"
        ) #. "c"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "nested block private assignments shadows private assignment of outer scope" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "outer" #= 1
        #: self_ "inner" #= block_
          ( local_ "outer" #= 2
          #: self_ "shadow" #= local_ "outer"
          ) #. "shadow"
        ) #. "inner"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "nested block private assignment shadows private alias for outer public assignment" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "outer" #= "hello"
        #: self_ "inner" #= block_
          ( self_ "shadow" #= local_ "outer"
          #: local_ "outer" #= "bye"
          ) #. "shadow"
        ) #. "inner"
      e = "bye"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "public references in local definitions are bound to the defining scope" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "Var" #= 1
        #: local_ "enclosingVar" #= self_ "Var"
        #: self_ "nested" #= block_
          ( self_ "Var" #= 2
          #: self_ "a" #= local_ "enclosingVar"
          ) #. "a"
        ) #. "nested"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "definition errors in nested scopes are returned with errors in outer scopes" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "x" #= tup_
          ( self_ "a" #= 1
          #: self_ "a" #= 2
          )
        #: self_ "x" #= "abc"
        ) #. "x"
      e = [OlappedSet (self_ "a"), OlappedVis (local_ "x")]
      in fails (assertEqual (banner r) e) (expr r)
  ]
  
  
paths :: (Expr a, Lit b, Local b, Self b, Eq b, Show b) => (a -> Either [DefnError] b) -> Test
paths expr = test
  [ "nested components can be accessed by paths" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "a" #= block_ ( self_ "aa" #= 2 )
        ) #. "a" #. "aa"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "nested components can be defined for paths" ~: let
      r :: Expr a => a
      r = block_ ( self_ "a" #. "aa" #= 2 ) #. "a" #. "aa"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "public reference scopes to definition root when assigning path" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "f" #= "x"
        #: self_ "a" #. "f" #= self_ "f"
        ) #. "a" #. "f"
      e = "x"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "public reference scopes to definition root when assigning to long path" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "f" #= 2
        #: self_ "a" #. "f" #. "g" #= self_ "f"
        ) #. "a" #. "f" #. "g"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "components can access nested components via long paths" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba"
        #: local_ "y1" #= block_ ( self_ "a" #. "ab" #. "aba" #= 3 )
        ) #. "raba"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "subpaths of path-defined nested components can be referenced" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "a" #. "aa" #. "aaa" #= 2
        #: self_ "b" #= self_ "a" #. "aa"
        ) #. "b" #. "aaa"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "private references bind to root scope when assigning path" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "a" #. "f" #= local_ "f" 
        #: local_ "f" #= local_ "g"
        ) #. "a" #. "f"
      e = local_ "g"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "can make private assignments using paths" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "Var" #. "field" #= 2
        #: self_ "x" #= local_ "Var"
        ) #. "x" #. "field"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "assigning to a path overlapping with a defined value within same scope is forbidden" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "x" #= tup_ ( self_ "a" #= 1 )
        #: self_ "x" #. "b" #= 2
        )
      e = [OlappedSet (self_ "x")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "can assign to disjoint paths with shared prefix within a scope" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "x" #. "a" #= 1
        #: self_ "x" #. "b" #= 2
        #: self_ "y" #= self_ "x" #."a" #+ self_ "x" #. "b"
        ) #. "y"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
          
  , "can assign to disjoint parts of a private definition" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "x" #. "y" #. "z" #= "hi" 
        #: local_ "x" #. "yy" #= local_ "x" #. "y"
        #: self_ "ret" #= local_ "x" #. "yy" #. "z"
        ) #. "ret"
      e = "hi"
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "assigning to paths where a leaf definition is overlapped is forbidden" ~: let
      r :: Expr a => a
      r = block_ 
        ( local_ "x" #. "y" #. "z" #= tup_ ( self_ "x" #= "hi" )
        #: local_ "x" #. "y" #= tup_ ( self_ "abc" #= local_ "g" )
        #: self_ "ret" #= local_ "x" #. "yy" #. "z"
        ) #. "ret"
      e = [OlappedSet (self_ "y")]
      in fails (assertEqual (banner r) e) (expr r)

  , "assigning to a path through a value from an outer scope makes a shadowed definition with the updated path" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "x" #= block_ ( self_ "a" #= 1 )
        #: local_ "y" #= block_
          ( local_ "x" #. "b" #= 2
          #: self_ "return" #= local_ "x"
          ) #. "return"
        #: self_ "call" #= local_ "y" #. "a" #+ local_ "y" #. "b"
        ) #. "call"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "original value is not affected by shadowing update in nested scope" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "x" #= block_
          ( self_ "a" #= 2
          #: self_ "b" #= 1
          )
        #: local_ "y" #= block_
          ( local_ "x" #. "b" #= 2
          #: self_ "return" #= local_ "x"
          ) #. "return"
        #: self_ "call" #= local_ "x" #. "b" #+ local_ "y" #. "b"
        ) #. "call"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
        
  ]
    
tuple :: (Expr a, Lit b, Local b, Self b, Eq b, Show b) => (a -> Either [DefnError] b) -> Test
tuple expr = test
  [ "component definitions scope to enclosing block" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "a" #= "str"
        #: self_ "b" #= tup_
          (  self_ "f" #= local_ "a" )
        ) #. "b" #. "f"
      e = "str"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "component definitions are not publicly referable" ~: let
      r :: Expr a => a
      r = tup_
        ( self_ "a" #= 1
        #: self_ "b" #= tup_
          ( self_ "f" #= self_ "a" ) #. "f"
        ) #. "b"
      e = self_ "a"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "component definitions are not referable by private alias" ~: let
      r :: Expr a => a
      r = tup_
        ( self_ "b" #= tup_ ( self_ "bf" #= local_ "f" )
        #: self_ "f" #= local_ "g"
        ) #. "f"
      e = local_ "g"
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "public pun assigns outer declared public variable to local public field" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "b" #= 1
        #: self_ "x" #= tup_ ( self_ "b" ) #. "b" ) #. "x"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "private pun assigns declared variable in private scope to local public field" ~: let
      r :: Expr a => a
      r = tup_ ( local_ "x" ) #. "x"
      e = local_ "x"
      in parses (expr r) >>= assertEqual (banner r) e
        
  ]

extension :: (Expr a, Lit b, Eq b, Show b) => (a -> Either [DefnError] b) -> Test
extension expr = test
  [ "extended components override original" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "a" #= 2 #:
        self_ "b" #= self_ "a"
        ) # block_ ( self_ "a" #= 1 ) #. "b"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "override later of mutually-referencing 'default' definitions" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "a" #= self_ "b" #:
        self_ "b" #= self_ "a"
        ) # block_ ( self_ "b" #= 2 ) #. "a"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "override earlier of mutually-referencing 'default' definitions" ~: let
      r :: Expr a => a
      r = block_ (
        self_ "a" #= self_ "b" #:
        self_ "b" #= self_ "a"
        ) # block_ ( self_ "a" #= 1 ) #. "b"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
       
  , "nested components of extension override nested components of original" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "a" #= block_ ( self_ "aa" #= 0 )
        #: self_ "b" #= self_ "a" #. "aa"
        ) # block_ ( self_ "a" #. "aa" #= 1 ) #. "b"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "self references can be used in extension" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "w1" #= block_ ( self_ "a" #= 1 )
        #: self_ "w2" #= local_ "w1" # block_ ( self_ "b" #= self_ "a" )
        #: self_ "ret" #= self_ "w2" #. "b" #+ self_ "w2" #. "a"
        ) #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
  
  , "object fields alias not in scope for extensions" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "a" #= 2
        #: local_ "w1" #= block_ ( self_ "a" #= 1 )
        #: self_ "w2" #= local_ "w1" # block_ ( self_ "b" #= local_ "a" )
        ) #. "w2" #. "b"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "extension components of extended object can be accessed" ~: let
      r :: Expr a => a
      r = block_
        ( self_ "w1" #= block_ ( self_ "a" #= 1 )
        #: self_ "w2" #= self_ "w1" # block_ ( self_ "b" #= 2 )
        ) #. "w2" #. "b"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "extension private assignments do not shadow fields of original" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "original" #= block_
          ( local_ "priv" #= 1
          #: self_ "privVal" #= local_ "priv"
          )
        #: local_ "new" #= local_ "original" # block_ ( local_ "priv" #= 2 )
        #: self_ "call" #= local_ "new" #. "privVal"
        ) #. "call"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "extension can reference original version lexically" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "y" #= block_ ( self_ "a" #= 1 )
        #: self_ "call" #= local_ "y" # block_ 
          ( self_ "a" #= local_ "y" #. "a" ) #. "a"
        ) #. "call"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
 
  ]

patterns :: (Expr a, Lit b, Eq b, Show b) => (a -> Either [DefnError] b) -> Test
patterns expr = test
  [ "decomposition block assigns components of a value" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "obj" #= block_
          ( self_ "a" #= 2
          #: self_ "b" #= 3
          )
        #: tup_
          ( self_ "a" #= local_ "da"
          #: self_ "b" #= self_ "db"
          ) #= local_ "obj"
        #: self_ "ret" #= local_ "da" #- self_ "db"
        ) #. "ret"
      e = fromInteger (-1)
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "decomposed values are assigned to corresponding leaf paths" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "obj" #= block_
          ( self_ "fp" #= 1
          #: self_ "fz" #= 3
          #: self_ "fc" #= "xy"
          )
        #: tup_
          ( self_ "fp" #= self_ "gp"
          #: self_ "fz" #= self_ "gz"
          #: self_ "fc" #= self_ "gc"
          ) #= local_ "obj"
        ) #. "gc"
      e = "xy"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "decomposed values assignments are independent of declaration order" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "obj" #= block_
          ( self_ "fc" #= "xy"
          #: self_ "fz" #= 3
          #: self_ "fp" #= 1
          )
        #: tup_
          ( self_ "fc" #= self_ "gc"
          #: self_ "fz" #= self_ "gz"
          #: self_ "fp" #= self_ "gp"
          ) #= local_ "obj"
        ) #. "gc"
      e = "xy"
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "destructuring a component twice in the same decomposition block is forbidden" ~: let
      r :: Expr a => a
      r = block_ (
        tup_
          ( self_ "a" #= local_ "pa"
          #: self_ "a" #= self_ "pb"
          ) #= local_ "p"
        ) #. "pb"
      e = [OlappedMatch (self_ "a")]
      in fails (assertEqual (banner r) e) (expr r)

  , "components not deconstructed in a decomposition block can be assigned to a trailing path" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "obj" #= block_
          ( self_ "a" #= 2
          #: self_ "b" #= 3
          )
        #: self_ "d" # tup_ ( self_ "a" #= local_ "x" ) #= local_ "obj"
        #: self_ "ret" #= self_ "d" #. "b"
        ) #. "ret"
      e = 3
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "deconstructed components are assigned to corresponding paths when a trailing path is used" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "obj" #= block_
          ( self_ "a" #= 2
          #: self_ "b" #= 3
          )
        #: self_ "d" # tup_ ( self_ "a" #= local_ "x" ) #= local_ "obj"
        #: self_ "ret" #= local_ "x"
        ) #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "can assign an empty block to a trailing path if all components are deconstructed" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "obj" #= block_ ( self_ "a" #= 2 )
        #: local_ "x" # tup_ ( self_ "a" #= local_ "y" ) #= local_ "obj"
        #: self_ "ret" #= local_ "y"
        ) #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
          
  , "paths can be used to deconstruct nested components" ~: let
      r :: Expr a => a
      r = block_ 
        ( local_ "get" #= block_ ( self_ "f" #. "g" #= 4 )
        #: tup_ ( self_ "f" #. "g" #= local_ "set" ) #= local_ "get"
        #: self_ "ret" #= local_ "set"
        ) #. "ret"
      e = 4
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "multiple paths to disjoint nested components can be deconstructed" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "a" #= tup_
          ( self_ "x" #= tup_
            ( self_ "y1" #= 2
            #: self_ "y2" #= 3
            )
          )
        #: tup_
          ( self_ "x" #. "y1" #= local_ "a1"
          #: self_ "x" #. "y2" #= local_ "a2"
          ) #= local_ "a"
        #: self_ "ret" #= local_ "a1" #- local_ "a2"
        ) #. "ret"
      e = fromInteger (-1)
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "multiple disjoint long paths can be deconstructed" ~: let
      r :: Expr a => a
      r = block_
        ( tup_
            ( self_ "x" #. "z" #. "y" #= local_ "b1"
            #: self_ "x" #. "z" #. "yy" #= local_ "b2"
            ) #= local_ "a"
        #: local_ "a" #= block_
          ( self_ "x" #. "z" #. "y" #= "hello"
          #: self_ "x" #. "z" #. "yy" #= 34
          )
        #: self_ "ret" #= local_ "b2"
        ) #. "ret"
      e = 34
      in parses (expr r) >>= assertEqual (banner r) e
      
  , "destructured paths must not be duplicates" ~: let
      r :: Expr a => a
      r = block_
        ( tup_
            ( self_ "x" #. "z" #= local_ "b1"
            #: self_ "x" #. "z" #= local_ "b2"
            ) #= local_ "a"
        #: local_ "a" #= block_
          ( self_ "x" #. "z" #= "hello" )
        #: self_ "ret" #= local_ "b2"
        ) #. "ret"
      e = [OlappedMatch (self_ "z")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured long paths must not be duplicates" ~: let
      r :: Expr a => a
      r = block_
        ( tup_
            ( self_ "x" #. "z" #. "y" #= local_ "b1"
            #: self_ "x" #. "z" #. "y" #= local_ "b2"
            ) #= local_ "a"
        #: local_ "a" #= block_
          ( self_ "x" #. "z" #. "y" #= "hello" )
        #: self_ "ret" #= local_ "b2"
        ) #. "ret"
      e = [OlappedMatch (self_ "y")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured paths must be disjoint from other destructured components" ~: let
      r :: Expr a => a
      r = block_
        ( tup_
            ( self_ "x" #. "z" #. "y" #= local_ "b1"
            #: self_ "x" #= local_ "b2"
            ) #= local_ "a"
        #: local_ "a" #= block_
          ( self_ "x" #. "z" #. "y" #= "hello" )
        #: self_ "ret" #= local_ "b2" #. "z" #. "y"
        ) #. "ret"
      e = [OlappedMatch (self_ "x")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "destructured paths must be disjoint from other destructured paths" ~: let
      r :: Expr a => a
      r = block_
        ( tup_
            ( self_ "x" #. "z" #= local_ "b2"
            #: self_ "x" #. "z" #. "y" #= local_ "b1"
            ) #= local_ "a"
        #: local_ "a" #= block_
          ( self_ "x" #. "z" #= tup_ ( self_ "y" #= "hello" ) )
        #: self_ "ret" #= local_ "b2" #. "y"
        ) #. "ret"
      e = [OlappedMatch (self_ "z")]
      in fails (assertEqual (banner r) e) (expr r)
      
      
  , "destructured paths must be disjoint from other destructured components and paths" ~: let
      r :: Expr a => a
      r = block_
        ( tup_
            ( self_ "x" #. "z" #. "y" #= local_ "b1"
            #: self_ "x" #= local_ "c1"
            #: self_ "x" #. "z" #= local_ "b2"
            ) #= local_ "a"
        #: local_ "a" #= block_
          ( self_ "x" #. "z" #. "y" #= "hello" )
        #: self_ "ret" #= local_ "b2" #. "y"
        ) #. "ret"
      e = [OlappedMatch (self_ "x"), OlappedMatch (self_ "z")]
      in fails (assertEqual (banner r) e) (expr r)
      
  , "a public name pun in a decomposition block assigns a component to the corresponding public name" ~: let
      r :: Expr a => a
      r = block_ 
        ( tup_ ( self_ "a" ) #= local_ "o"
        #: local_ "o" #= tup_ ( self_ "a" #= 1 )
        ) #. "a"
      e = 1
      in parses (expr r) >>= assertEqual (banner r) e
        
  , "a private name pun in a decomposition block assigns a component to the corresponding private name" ~: let
      r :: Expr a => a
      r = block_ 
        ( tup_ ( local_ "a" ) #= local_ "o"
        #: local_ "o" #= tup_ ( self_ "a" #= 2 )
        #: self_ "ret" #= local_ "a"
        ) #. "ret"
      e = 2
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "a private path pun can be used to destructure a nested component to the corresponding local path" ~: let
      r :: Expr a => a
      r = block_
        ( tup_ ( local_ "a" #. "f" #. "g" ) #= block_
          ( self_ "a" #. "f" #. "g" #= 4 )
        #: self_ "ret" #= local_ "a"
        ) #. "ret" #. "f" #. "g"
      e = 4
      in parses (expr r) >>= assertEqual (banner r) e
    
  , "patterns can be nested in decomposition blocks" ~: let
      r :: Expr a => a
      r = block_
        ( local_ "y1" #= block_
          ( self_ "a" #= block_
            ( self_ "aa" #= 3
            #: self_ "ab" #= block_ ( self_ "aba" #= 4 )
            )
          )
        #: tup_
          ( self_ "a" #= tup_
            ( self_ "aa" #= self_ "da"
            #: self_ "ab" #= tup_ ( self_ "aba" #= self_ "daba" )
            )
          ) #= local_ "y1"
        #: self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba"
        #: self_ "ret" #= self_ "raba" #- self_ "daba"
        ) #. "ret"
      e = 0
      in parses (expr r) >>= assertEqual (banner r) e
      
  ]
