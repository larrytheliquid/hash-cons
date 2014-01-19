{-# LANGUAGE TypeSynonymInstances , FlexibleInstances #-}
module HashCons.Term where
import HashCons.BiMap
import Prelude hiding ( pi )
import Control.Monad.State

----------------------------------------------------------------------

type Ident = String
wildcard = "_"

class Term a where
  pi  :: Ident -> a -> a -> a
  lam :: Ident -> a -> a
  app :: a -> a -> a
  var :: Ident -> a
  label :: Ident -> a

pis :: Term a => [(Ident , a)] -> a -> a
pis ((nm , _A) : []) _B = pi nm _A _B
pis ((nm , _A) : nm_As) _B = pi nm _A (pis nm_As _B)
pis [] _B = error "need at least 1 pis domain"

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
  deriving ( Show , Eq )

instance Term Expr where
  pi = EPi
  lam = ELam
  app = EApp
  var = EVar
  label = ELabel

count :: Expr -> Int
count (EPi _ _A _B) = 1 + count _A + count _B
count (ELam _ bd) = 1 + count bd
count (EApp f a) = 1 + count f + count a
count (EVar _) = 1
count (ELabel _) = 1

----------------------------------------------------------------------

type NodeId = Int
type DAG = BiMap Node
type NodeM = State DAG NodeId

data Node =
    NPi Ident NodeId NodeId
  | NLam Ident NodeId
  | NApp NodeId NodeId
  | NVar Ident
  | NLabel Ident
  deriving ( Show , Eq , Ord )

hashcons :: Node -> NodeM
hashcons n = do
  g <- get
  case lookupKey n g of
    Nothing -> do
      let (k , g') = insert n g
      put g'
      return k
    Just k -> return k

instance Term NodeM where
  pi nm _A _B = do
     _A <- _A
     _B <- _B
     hashcons $ NPi nm _A _B
  lam nm bd = do
    bd <- bd
    hashcons $ NLam nm bd
  app f a = do
    f <- f
    a <- a
    hashcons $ NApp f a
  var nm = hashcons $ NVar nm
  label nm = hashcons $ NLabel nm

runNodeM :: NodeM -> (NodeId , DAG)
runNodeM m = runState m empty

----------------------------------------------------------------------