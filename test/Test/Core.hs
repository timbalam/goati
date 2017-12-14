{-# LANGUAGE OverloadedStrings #-}
module Test.Core
  ( tests
  )
  where

import qualified Core
import qualified Types.Core as Core
import Types.Classes
import Types.Parser.Short
--import qualified Types.Error as E

import qualified Data.Map as M
import Control.Monad.Trans
import Test.HUnit hiding ( Label )
import Bound --( toScope, Var(..) )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","

parses :: Syntax -> IO (Core.Expr (Vis Core.Id))
parses =
  maybe
    (ioError (userError "expr"))
    return
    . Core.getresult . Core.expr
  
  
fails :: (e -> Assertion) -> Syntax -> Assertion
fails _ =
  maybe
    (return ())
    (ioError . userError . show)
    . Core.getresult . Core.expr
    
    
seScope = toScope . toScope . toScope
seF = F . F . F
enScope = toScope . toScope
enF = F . F
    

tests =
  test
    [ "number"  ~: let
        r = 1
        e = Core.Number 1
        in
        parses r >>= assertEqual (banner r) e
           
    , "string" ~: let
        r = "test"
        e = Core.String "test"
        in
        parses r >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r = self' "public"
        e = (Core.Var . Pub) (Label "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env' "private"
        e = Core.Var (Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env' "var" #. "field"
        e = Core.Var (Priv "var") `Core.At` Label "field"
        in
        parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "assign public field" ~: let 
          r = block' [ self' "public" #= 1 ]
          e = (Core.Block [] . M.fromList) [
            (Label "public", seScope (Core.Number 1))
            ]
          in
          parses r >>= assertEqual (banner r) e
       
        , "assign private field" ~: let
            r = block' [ env' "private" #= 1 ]
            e = Core.Block [enScope (Core.Number 1)] M.empty
            in
            parses r >>= assertEqual (banner r) e
          
        , "backwards reference" ~: let
            r = block' [ env' "one" #= 1, self' "oneRef" #= env' "one" ]
            e = (Core.Block [enScope (Core.Number 1)]
              . M.fromList) [
              (Label "oneRef", (seScope . Core.Var . F . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "forwards reference" ~: let
            r = block' [ self' "twoRef" #= env' "two", env' "two" #= 2 ]
            e = (Core.Block [enScope (Core.Number 2)]
              . M.fromList) [
              (Label "twoRef", (seScope . Core.Var . F . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = block' [ env' "selfRef" #= env' "selfRef" ]
            e = Core.Block [(enScope . Core.Var . F) (B 0)] M.empty
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = block' [
              env' "selfRef" #= env' "selfRef",
              self' "loop" #= env' "selfRef"
              ]
            e = (Core.Block [(enScope . Core.Var . F) (B 0)] . M.fromList) [
              (Label "loop",
                (seScope . Core.Var . F . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "private referencing public" ~: let
            r = block' [
              self' "public" #= 1,
              env' "notPublic" #= self' "public"
              ]
            e = (Core.Block [
              (enScope . Core.Var . B) (Label "public")
              ]. M.fromList) [
              (Label "public", seScope (Core.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "public referenced as private" ~: let
            r = block' [
              self' "public" #= 1,
              self' "publicAgain" #= env' "public"
              ]
            e = (Core.Block []. M.fromList) [
              (Label "public", seScope (Core.Number 1)),
              (Label "publicAgain",
                (seScope . Core.Var . B) (Label "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "object" #= block' [ self' "refOuter" #= env' "outer" ]
              ]
            e = (Core.Block [enScope (Core.Number 1)]
              . M.fromList) [
              (Label "object",
                (seScope . Core.Block [] . M.fromList) [
                  (Label "refOuter",
                    (seScope . Core.Var . seF . F . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "unbound variable" ~: let
            r = block' [
              self' "here" #= 2,
              self' "refMissing" #= env' "missing"
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "here", seScope (Core.Number 2)),
              (Label "refMissing", (seScope . Core.Var . seF)
                (Priv "missing"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "declared variable" ~: let
            r = block' [
              Declare (self' "unset"),
              self' "set" #= 1
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "unset", seScope Core.Undef),
              (Label "set", seScope (Core.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference declared variable" ~: let
            r = block' [
              Declare (env' "a"),
              self' "b" #= env' "a"
              ]
            e = (Core.Block [enScope Core.Undef] . M.fromList) [
              (Label "b",
                (seScope . Core.Var . F . F) (B 0))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign public path" ~: let
            r = block' [ self' "a" #. "field" #= 1 ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", seScope
                ((Core.Block [] . M.fromList) [
                  (Label "field", seScope (Core.Number 1))
                  ] `Core.Concat`
                  ((Core.Var . F) (B ()) `Core.Fix` Label "field")))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= self' "f" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", seScope
                ((Core.Block [] . M.fromList) [
                (Label "f", (seScope . Core.Var . seF . B)
                  (Label "f"))
                ] `Core.Concat`
                ((Core.Var . F) (B ()) `Core.Fix` Label "f")))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign expression with public references to long path" ~: let
            r = block' [ self' "a" #. "f" #. "g" #= self' "f" # self' "g" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", seScope ((Core.Block [] . M.fromList) [
                (Label "f", seScope ((Core.Block [] . M.fromList) [
                  (Label "g", seScope
                    ((Core.Var . seF . seF . B) (Label "f") `Core.Update`
                      (Core.Var . seF . seF . B) (Label "g")))
                  ] `Core.Concat`
                  ((Core.Var . F) (B ()) `Core.Fix` Label "g")))
                ] `Core.Concat`
                ((Core.Var . F) (B ()) `Core.Fix` Label "f")))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= env' "f" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", seScope ((Core.Block [] . M.fromList) [
                (Label "f",
                  (seScope . Core.Var . seF . seF) (Priv "f"))
                ] `Core.Concat`
                ((Core.Var . F) (B ()) `Core.Fix` Label "f")))
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = block' [ env' "var" #. "field" #= 2 ]
            e = Core.Block [
              enScope ((Core.Block [] . M.fromList) [
                (Label "field",
                  seScope (Core.Number 2))
                ] `Core.Concat`
                ((Core.Var . enF) (Priv "var") `Core.Fix`
                  Label "field"))
              ] M.empty
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadow private variable" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "inner" #= block' [
                env' "outer" #= 2,
                self' "shadow" #= env' "outer"
                ]
              ]
            e = (Core.Block [enScope (Core.Number 1)]
              . M.fromList) [
              (Label "inner",
                (seScope . Core.Block [
                  enScope (Core.Number 2)
                  ] . M.fromList) [
                  (Label "shadow", (seScope . Core.Var . F . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "shadow public variable" ~: let
            r = block' [ 
              self' "outer" #= "hello",
              self' "inner" #= block' [
                self' "shadow" #= env' "outer",
                env' "outer" #= "bye"
                ] #. "shadow"
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "outer",
                seScope (Core.String "hello")),
              (Label "inner", seScope
                (((Core.Block [
                  enScope (Core.String "bye")
                  ] . M.fromList) [
                  (Label "shadow",
                    (seScope . Core.Var . F
                      . F) (B 0))
                  ]) `Core.At` Label "shadow"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "shadowing update public using path" ~: let
            r = block' [
              self' "inner" #= block' [
                self' "var" #. "g" #= env' "y"
                ]
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "inner",
                (seScope . Core.Block []
                  . M.fromList) [
                  (Label "var", seScope
                    ((Core.Block [] . M.fromList) [
                      (Label "g",
                        (seScope . Core.Var . seF . seF . seF) (Priv "y"))
                      ] `Core.Concat`
                      ((Core.Var . F) (B ()) `Core.Fix` Label "g")))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadowing private using path" ~: let
            r = block' [
              env' "outer" #= block' [ self' "g" #= "hello" ],
              self' "inner" #= block' [ env' "outer" #. "g" #= "bye" ]
              ]
            e = (Core.Block [
              (enScope . Core.Block [] . M.fromList) [
                (Label "g",
                  seScope (Core.String "hello"))
                ]
              ] . M.fromList) [
              (Label "inner",
                seScope (Core.Block [
                  enScope ((Core.Block [] . M.fromList) [
                    (Label "g", seScope (Core.String "bye"))
                    ] `Core.Concat`
                    ((Core.Var . seF . F) (B 0) `Core.Fix`
                      Label "g"))
                  ] M.empty))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        ]
    
    , "update" ~: let
        r = (block' [
          self' "a" #= 2,
          self' "b" #= env' "a"
          ] # env' "y")
        e = (Core.Block [] . M.fromList) [
          (Label "a",
            seScope (Core.Number 2)), 
          (Label "b",
            (seScope . Core.Var . B) (Label "a"))
          ] `Core.Update` Core.Var (Priv "y")
        in
        parses r >>= assertEqual (banner r) e
      
    , "destructuring" ~: let
        r = block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock' [
            self' "a" #= self' "da",
            self' "b" #= self' "db"
            ] #= env' "obj"
          ]
        e = (Core.Block [
          (enScope . Core.Block [] . M.fromList) [
            (Label "a", seScope (Core.Number 2)),
            (Label "b", seScope (Core.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", seScope
            ((Core.Var . F . F) (B 0) `Core.At` Label "a")),
          (Label "db", seScope
            ((Core.Var . F . F) (B 0) `Core.At` Label "b"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring unpack" ~: let
        r = block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock'' [ self' "a" #= self' "da" ] (self' "db") #= env' "obj"
          ] #. "b"
        e = (Core.Block [
          (enScope . Core.Block [] . M.fromList) [
            (Label "a", seScope (Core.Number 2)),
            (Label "b", seScope (Core.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", seScope
            ((Core.Var . F . F) (B 0) `Core.At` Label "a")),
          (Label "b", seScope
            ((Core.Var . F . F) (B 0) `Core.Fix` Label "a"))
          ] `Core.At` Label "b"
        in parses r >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r = block' [
          env' "y1" #= block' [
            self' "a" #= block' [
              self' "aa" #= 3,
              self' "ab" #= block' [ self' "aba" #= 4 ]
              ]
            ],
          setblock' [
            self' "a" #. "aa" #= self' "da",
            self' "a" #. "ab" #. "aba" #= self' "daba"
            ] #= env' "y1", 
          self' "raba" #=  env' "y1" #. "a" #. "ab" #. "aba"
          ]
        e = (Core.Block [
          (enScope . Core.Block [] . M.fromList) [
            (Label "a", (seScope . Core.Block [] 
              . M.fromList) [
              (Label "aa", seScope (Core.Number 3)),
              (Label "ab", (seScope . Core.Block []
                . M.fromList) [
                (Label "aba", seScope (Core.Number 4))
                ])
              ])
            ]
          ] . M.fromList) [
          (Label "da", seScope
            (((Core.Var . F . F) (B 0) `Core.At` Label "a") `Core.At`
              Label "aa")),
          (Label "daba", seScope
            ((((Core.Var . F . F) (B 0) `Core.At` Label "a") `Core.At`
              Label "ab") `Core.At` Label "aba")),
          (Label "raba", seScope
            ((((Core.Var . F . F) (B 0) `Core.At` Label "a") `Core.At`
              Label "ab") `Core.At` Label "aba"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "parent scope binding" ~: let
        r = block' [
          self' "inner" #= 1,
          env' "parInner" #= self' "inner",
          self' "outer" #= block' [
            self' "inner" #= 2,
            self' "a" #= env' "parInner"
            ]
          ]
        e = (Core.Block [
          (enScope . Core.Var . B) (Label "inner")
          ] . M.fromList) [
          (Label "inner", seScope (Core.Number 1)),
          (Label "outer", (seScope . Core.Block [] . M.fromList) [
            (Label "inner", seScope (Core.Number 2)),
            (Label "a", (seScope . Core.Var . seF . F . F) (B 0))
            ])
          ]
        in parses r >>= assertEqual (banner r) e
      
    , "self referencing definition" ~: let
        r = block' [
          env' "y" #= block' [
            self' "a" #= env' "y" #. "b",
            self' "b" #= 1
            ],
          self' "z" #= env' "y" #. "a"
          ]
        e = (Core.Block [
          (enScope . Core.Block [] . M.fromList) [
            (Label "a", seScope
              ((Core.Var . seF . F) (B 0) `Core.At` Label "b")),
            (Label "b", seScope (Core.Number 1))
            ]
          ] . M.fromList) [
            (Label "z", seScope
              ((Core.Var . F . F) (B 0) `Core.At` Label "a"))
            ]
        in parses r >>= assertEqual (banner r) e
          
    , "application to referenced outer scope" ~: let
        r = block' [
          env' "y" #= block' [
            self' "a" #= 1,
            env' "b" #= 2,
            self' "x" #= block' [ self' "a" #= env' "b" ]
            ],
          self' "a" #= env' "y" # (env' "y" #. "x") #. "a"
          ]
        e = (Core.Block [
          (Scope . Scope . Core.Block [enScope (Core.Number 2)] . M.fromList) [
            (Label "a", seScope (Core.Number 1)),
            (Label "x", (seScope . Core.Block [] . M.fromList) [
              (Label "a", (seScope . Core.Var . seF . F . F) (B 0))
              ])
            ]
          ] . M.fromList) [
          (Label "a", seScope
            (((Core.Var . F . F) (B 0) `Core.Update`
              ((Core.Var . F . F) (B 0) `Core.At` Label "x")) `Core.At`
                Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "application to nested object" ~: let
        r = block' [
          env' "y" #= block' [
            self' "a" #= 1,
            self' "x" #= block' [
              self' "a" #= 2,
              Declare (self' "x")
              ]
            ],
          self' "a" #= env' "y" #. "x" # (env' "y" #. "a")
          ]
        e = (Core.Block [
          (enScope . Core.Block [] . M.fromList) [
            (Label "a", seScope (Core.Number 1)),
            (Label "x", (seScope . Core.Block [] . M.fromList) [
              (Label "a", seScope (Core.Number 2)),
              (Label "x", seScope Core.Undef)
              ])
            ]
          ] . M.fromList) [
          (Label "a", seScope
            (((Core.Var . F . F) (B 0) `Core.At` Label "x") `Core.Update`
              ((Core.Var . F . F) (B 0) `Core.At` Label "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]