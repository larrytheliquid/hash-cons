module HashCons.Term where

----------------------------------------------------------------------

type Ident = String

class Term a where
  pi  :: Ident -> a -> a -> a
  lam :: Ident -> a -> a
  app :: a -> a -> a
  var :: Ident -> a
  label :: Ident -> a

apps :: Term a => [a] -> a
apps (x : []) = x
apps (x : y : xs) = apps (app x y : xs)
apps [] = error "need at least 1 apps argument"

lams :: Term a => [Ident] -> a -> a
lams (nm : []) bd = lam nm bd
lams (nm : nms) bd = lam nm (lams nms bd)
lams [] bd = error "need at least 1 lams parameter"

----------------------------------------------------------------------

data Expr =
    EPi Ident Expr Expr
  | ELam Ident Expr
  | EApp Expr Expr
  | EVar Ident
  | ELabel Ident
  deriving ( Show , Eq , Ord )

instance Term Expr where
  pi = EPi
  lam = ELam
  app = EApp
  var = EVar
  label = ELabel

----------------------------------------------------------------------