{-# LANGUAGE OverloadedStrings #-}

module Syntax.Class.Import
  ( tests
  )
  where

import My.Eval (simplify, K)
import My.Types.Expr
import My.Types.Syntax.Class hiding (Expr)
import My.Syntax.Parser (Printer, showP)
import My.Syntax.Import (Src(..), Kr(..))
import qualified My.Types.Parser as P
import My.Parser (ShowMy, showMy)
import My.Syntax (loadexpr, KeySource(..))
import My.Syntax.Expr
import Control.Exception
import Test.HUnit
  
  
banner :: Printer -> String
banner r = "For " ++ showP r ","

run
 :: Kr
      (BlockBuilder (Expr K (P.Vis (Nec Ident) Key)))
      (E (Expr K (P.Vis (Nec Ident) Key)))
  -> IO (Expr K (P.Vis (Nec Ident) Key))
run r = simplify <$> loadexpr (runKr r User) ["test/data/Import"]

tests =
  test
    [ "import resolves to local .my file with same name" ~: let
        r :: Syntax a => a
        r = use_ "import" #. "test"
        e = Prim (String "imported")
        in
        run r >>= assertEqual (banner r) e
        
    , "imported file resolves nested imports to directory with same name" ~: let
        r :: Syntax a => a
        r = use_ "chain" #. "test"
        e = Prim (String "nested")
        in
        run r >>= assertEqual (banner r) e
    ]
    
    