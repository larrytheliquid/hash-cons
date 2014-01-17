module Term where

----------------------------------------------------------------------

type Ident = String

class Term a where
  pi  :: a -> Ident -> a -> a
  lam :: Ident -> a -> a
  app :: a -> a -> a
  var :: Ident -> a

----------------------------------------------------------------------

data Expr =
    EPi Expr Ident Expr
  | ELam Ident Expr
  | EApp Expr Expr
  | EVar Ident
  deriving ( Show , Eq , Ord )

instance Term Expr where
  pi = EPi
  lam = ELam
  app = EApp
  var = EVar

----------------------------------------------------------------------