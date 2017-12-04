{-# LANGUAGE OverloadedStrings #-}
module Test.Eval
  ( tests
  )
  where

import qualified Core
import qualified Eval as Core
import qualified Types.Core as Core
import Types.Classes
import Types.Parser.Short
--import qualified Types.Error as E

import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: Core.Expr (Vis Tag) -> IO (Core.Expr (Vis Tag))
run =
  maybe
    (ioError (userError "eval"))
    return
    . Core.eval


fails :: (e -> Assertion) -> Core.Expr (Vis Tag) -> Assertion
fails _ =
  maybe
    (return ())
    (ioError . userError . showMy)
    . Core.eval
  
  
parses :: Expr (Vis Tag) -> IO (Core.Expr (Vis Tag))
parses =
  maybe
    (ioError (userError "expr"))
    return
    . Core.getresult . Core.expr

    
type E = Expr (Vis Tag)


tests =
  test
    [ "add" ~: do
        r <- parses (1 #+ 1)
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "subtract" ~: do
        r <- parses (1 #- 2)
        let e = Core.Number (-1)
        run r >>= assertEqual (banner r) e
          
    , "public variable" ~: do
        r <- parses (Block [ self "pub" #= 1 ] #. "pub")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
       
    , "private variable" ~: do
        r <- parses (Block [ env "priv" #= 1 ] #. "priv")
        fails (assertEqual "Unbound var: priv" "priv") r
    
    , "private variable access backward" ~: do
        r <- parses (Block [
          env "priv" #= 1,
          self "pub" #= env "priv"
          ] #. "pub")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
        
    , "private variable access forward" ~: do
        r <- parses (Block [
          self "pub" #= env "priv",
          env "priv" #= 1
          ] #. "pub")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "private access of public variable" ~: do
        r <- parses (Block [
          self "a" #= 1,
          self "b" #= env "a"
          ] #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "private access in nested scope of public variable" ~: do
        r <- parses (Block [
          self "a" #= 1,
          env "object" #= Block [ self "b" #= env "a" ],
          self "c" #= env "object" #. "b"
          ] #. "c")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "access backward public variable from same scope" ~: do
        r <- parses (Block [
          self "b" #= 2,
          self "a" #= self "b"
          ] #. "a")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "access forward public variable from same scope" ~: do
        r <- parses (Block [
          self "a" #= self "b",
          self "b" #= 2
          ] #. "a")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "unbound variable" ~: do
        r <- parses (Block [
          self "a" #= 2,
          self "b" #= env "c" #+ 1
          ] #. "b")
        fails (assertEqual "Unbound var: b" "b") r
          
    , "undefined variable" ~: do
        r <- (parses . Block) [
          Declare (self "a"),
          self "b" #= 1
          ]
        let
          r1 = r `Core.At` "b"
          e1 = Core.Number 1
          r2 = r `Core.At` "a"
        run r1 >>= assertEqual (banner r1) e1
        fails (assertEqual "Unbound var : a" "a") r2
         
    , "unset variable forwards" ~: do
        r <- parses (Block [
          env "c" #= 1,
          env "b" #= Block [
            Declare (env "c"),
            self "a" #= env "c"
            ],
          self "ba" #= env "b" #. "a"
          ] #. "ba")
        fails (assertEqual "Unbound var: c" "c") r
          
    , "unset variable backwards" ~: do
        r <- parses (Block [
          env "c" #= 1,
          env "b" #= Block [
            self "a" #= env "c",
            Declare (env "c")
            ],
          self "ba" #= env "b" #. "a"
          ] #. "ba")
        fails (assertEqual "Unbound var: c" "c") r
    
    , "application  overriding public variable" ~: do
        r <- parses (Block [
          self "a" #= 2,
          self "b" #= self "a" #+ 1
          ] # Block [ self "a" #= 1 ] #. "b")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "default definition forward" ~: do
        r <- parses (Block [
          self "a" #= self "b" #- 1,
          self "b" #= self "a" #+ 1
          ] # Block [ self "b" #= 2 ] #. "a")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "default definition backward" ~: do
        r <- parses (Block [
          self "a" #= self "b" #- 1,
          self "b" #= self "a" #+ 1
          ] # Block [ self "a" #= 2 ] #. "b")
        let e = Core.Number 3
        run r >>= assertEqual (banner r) e
          
    , "route getter" ~: do
        r <- parses (Block [
          self "a" #= Block [ self "aa" #= 2 ]
          ] #. "a" #. "aa")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "route setter" ~: do
        r <- parses (Block [ self "a" #. "aa" #= 2 ] #. "a" #. "aa")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "application overriding nested property" ~: do
        r <- parses (Block [
          self "a" #= Block [ self "aa" #= 0 ],
          self "b" #= self "a" #. "aa"
          ] # Block [ self "a" #. "aa" #= 1 ] #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "shadowing update" ~: do
        r <- parses (Block [
          env "outer" #= Block [ self "a" #= 1 ],
          self "inner" #= Block [
            env "outer" #. "b" #= 2,
            self "ab" #= env "outer" #. "a" #+ env "outer" #. "b"
            ]
          ] #. "inner" #. "ab")
        let e = Core.Number 3
        run r >>= assertEqual (banner r) e
          
    , "shadowing update 2" ~: do
        r <- parses (Block [
          env "outer" #= Block [
            self "a" #= 2,
            self "b" #= 1
            ],
          self "inner" #= Block [ self "outer" #. "b" #= 2 ],
          self "ab" #= env "outer" #. "a" #+ env "outer" #. "b"
          ] #. "ab")
        let e = Core.Number 3
        run r >>= assertEqual (banner r) e
          
    , "destructuring" ~: do
        r <- parses (Block [
          env "obj" #= Block [
            self "a" #= 2,
            self "b" #= 3
            ],
          SetBlock [
            self "a" #= self "da",
            self "b" #= self "db"
            ] #= env "obj"
          ])
        let
          r1 = r `Core.At` "da"
          e1 = Core.Number 2
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` "db"
          e2 = Core.Number 3
        run r2 >>= assertEqual (banner r2) e2
            
    , "destructuring unpack" ~: do
        r <- parses (Block [
          env "obj" #= Block [
            self "a" #= 2,
            self "b" #= 3
            ],
          SetConcat [] (self "d") #= env "obj"
          ] #. "d" #. "b")
        let
          e = Core.Number 3
        run r >>= assertEqual (banner r) e
          
    , "nested destructuring" ~: do
        r <- parses (Block [
          env "y1" #= Block [
            self "a" #= Block [
              self "aa" #= 3,
              self "ab" #= Block [ self "aba" #= 4 ]
              ]
            ],
          SetBlock [
            self "a" #. "aa" #= self "da",
            self "a" #. "ab" #. "aba" #= self "daba"
            ] #= env "y1",
          self "raba" #= env "y1" #. "a" #. "ab" #. "aba"
          ])
        let
          r1 = r `Core.At` "raba"
          e1 = Core.Number 4
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` "daba"
          e2 = Core.Number 4
        run r2 >>= assertEqual (banner r2) e2
            
    , "unpack visible publicly" ~: do
        r <- (parses . Block) [
          env "w1" #= Block [ self "a" #= 1 ],
          self "w2" #= Concat [
            Block [ self "b" #= self "a" ],
            env "w1"
            ],
          self "w3" #= self "w2" #. "a"
          ]
        let
          r1 = (r `Core.At` "w2") `Core.At` "b"
          e1 = Core.Number 1
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` "w3"
          e2 = Core.Number 1
        run r2 >>= assertEqual (banner r2) e2
          
    , "unpack visible privately" ~: do
        r <- parses (Block [
          env "w1" #= Block [ self "a" #= 1 ],
          self "w2" #= Concat [
            Block [ self "b" #= env "a" ],
            env "w1"
            ]
          ] #. "w2" #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "local private variable unpack visible publicly" ~: do
      r <- parses (Block [
        self "w1" #= Block [ self "a" #= 1 ],
        self "w2" #= Concat [
          Block [ self "b" #= self "a" ],
          env "w1"
          ]
        ] #. "w2" #. "a")
      let e = Core.Number 1
      run r >>= assertEqual (banner r) e
          
    , "access member of object with local public variable unpack" ~: do
      r <- parses (Block [
        self "w1" #= Block [ self "a" #= 1 ],
        self "w2" #= Concat [
          self "w1",
          Block [ self "b" #= 2 ]
          ]
        ] #. "w2" #. "b")
      let e = Core.Number 2
      run r >>= assertEqual (banner r) e
          
    , "local public variable unpack visible privately" ~: do
        r <- parses (Block [
          self "w1" #= Block [ self "a" #= 1 ],
          self "w2" #= Concat [
            self "w1",
            Block [ self "b" #= env "a" ]
            ]
          ] #. "w2" #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
            
    , "parent scope binding" ~: do
        r <- parses (Block [
          self "inner" #= 1,
          env "parInner" #= self "inner",
          self "outer" #= Block [
            self "inner" #= 2,
            self "a" #= env "parInner"
            ]       
          ] #. "outer" #. "a")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "unpack scope binding" ~: do
        r <- parses (Block [
          env "inner" #= Block [
            env "var" #= 1,
            self "innerVar" #= env "var"
            ],
          env "outer" #= Concat [
            Block [ env "var" #= 2 ],
            env "inner"
            ],
          self "a" #= env "outer" #. "innerVar"
          ] #. "a")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "self referencing definition" ~: do
        r <- parses (Block [
          env "y" #= Block [
            self "a" #= env "y" #. "b",
            self "b" #= 1
            ],
          self "z" #= env "y" #. "a"
          ] #. "z")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "application to referenced outer scope" ~: do
        r <- parses (Block [
          env "y" #= Block [
            self "a" #= 1,
            env "b" #= 2,
            self "x" #= Block [ self "a" #= env "b" ]
            ],
          self "a" #= env "y" # (env "y" #. "x") #. "a"
          ] #. "a")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "application to nested object" ~: do
        r <- parses (Block [
          env "y" #= Block [
            self "a" #= 1,
            self "x" #= Block [
              self "a" #= 2,
              Declare (self "x")
              ]
            ],
          self "a" #= env "y" #. "x" # env "y" #. "a"
          ] #. "a")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
    
    ]