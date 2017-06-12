module Types.Short
where
import qualified Types.Parser as T

lident' = T.Lident . T.Ident
lsref' = T.Lroute . T.Atom . T.Ident
lref' x y = T.Lroute (x `T.Route` T.Ident y)
lident = T.Laddress . lident'
lsref = T.Laddress . lsref'
lref x y = T.Laddress (x `lref'` y)
rident = T.Rident . T.Ident
rsref = T.Rroute . T.Atom . T.Ident
rref x y = T.Rroute (x `T.Route` T.Ident y)
plainsref = T.PlainRoute . T.Atom . T.Ident
plainref x y = T.PlainRoute (x `T.Route` T.Ident y)
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