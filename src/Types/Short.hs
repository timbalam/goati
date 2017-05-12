module Types.Short
where
import qualified Types.Parser as T

lident' = T.Lident . T.Ident
lsref' = T.Lroute . T.Atom . T.Ref . T.Ident
lskey' = T.Lroute . T.Atom . T.Key
lref' x y = T.Lroute (x `T.Route` T.Ref (T.Ident y))
lkey' x y = T.Lroute (x `T.Route` T.Key y)
lident = T.Laddress . lident'
lsref = T.Laddress . lsref'
lskey = T.Laddress . lskey'
lref x y = T.Laddress (x `lref'` y)
lkey x y = T.Laddress (x `lkey'` y)
rident = T.Rident . T.Ident
rsref = T.Rroute . T.Atom . T.Ref . T.Ident
rskey = T.Rroute . T.Atom . T.Key
rref x y = T.Rroute (x `T.Route` T.Ref (T.Ident y))
rkey x y = T.Rroute (x `T.Route` T.Key y)
plainsref = T.PlainRoute . T.Atom . T.Ref . T.Ident
plainskey = T.PlainRoute . T.Atom . T.Key
plainref x y = T.PlainRoute (x `T.Route` T.Ref (T.Ident y))
plainkey x y = T.PlainRoute (x `T.Route` T.Key y)
_and_ = T.Binop T.And
_or_ = T.Binop T.Or
_add_ = T.Binop T.Add
_sub_ = T.Binop T.Sub
_prod_ = T.Binop T.Prod
_div_ = T.Binop T.Div
_pow_ = T.Binop T.Pow
_eq_ = T.Binop T.Eq
_ne_ = T.Binop T.Ne
_gt_ = T.Binop T.Gt
_lt_ = T.Binop T.Lt
_ge_ = T.Binop T.Ge
_le_ = T.Binop T.Le