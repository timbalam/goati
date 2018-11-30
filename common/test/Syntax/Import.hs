{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Syntax.Import
  ( tests )
  where

import Goat.Syntax.Class
import Goat.Syntax.Parser (Printer, showP)
import Test.HUnit

banner :: Printer -> String
banner r = "For " ++ showP r ","


check :: Either [StaticError Ident] a -> IO a
check = either 
  (fail . displayErrorList displayStaticError)
  return


tests
 :: ( Preface a, Rec (ModuleStmt a)
    , Expr (Rhs (ModuleStmt a))
    , Lit b, Eq b, Show b
    )
 => (a
     -> (FilePath -> IO Maybe a)
     -> IO (Either [StaticError Ident] b))
 -> FilePath
 -> Test
tests load dir =
  test
    [ "parse a plain module" ~: let
        r
         :: ( Module a, Rec (ModuleStmt a)
            , Expr (Rhs (ModuleStmt a))
            ) => a
        r = module_ [ self_ "run" #= "module" ]
        e = "module"
        in run [] >>= load r >>= assertEqual (banner r) e
    
    , "import resolves to local .my file with same name" ~: let
        r, ext
         :: ( Module a, Rec (ModuleStmt a)
            , Expr (Rhs (ModuleStmt a))
            ) => a
        ext = module_ [ self_ "test" #= "imported" ]
        r = 
          extern_ [ "import" #= "./ext.gt" ]
          (module_ [ self_ "run" #= use_ "import" #. "test" ])
        e = "imported"
        in
          run [("ext.gt", ext)] (mod r) >>= assertEqual (banner r) e
        
    , "imported file resolves nested imports to directory with same name" ~: let
        r, ext, chain
         :: ( Module a, Rec (ModuleStmt a)
            , Expr (Rhs (ModuleStmt a))
            ) => a
        r = extern_ [ "chain" #= "./chain.gt" ]
          (module_ [ self_ "run" #= use_ "chain" #. "test" ])
        chain = extern [ "import" #= "./chain/ext.gt" ]
          (module_ [ self_ "test" #= use_ "import" #. "test" ])
        ext = module_ [ self_ "test" #= "nested" ]
        e = "nested"
        in run 
          [ ("./chain.gt", chain )
          , ("./chain/ext.gt", ext )
          ] (mod r) >>= assertEqual (banner r) e
    ]
    
    