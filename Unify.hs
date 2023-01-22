{-# LANGUAGE NoMonomorphismRestriction #-}

module Unify where

import Control.Monad.Trans.State
import Data.Bifunctor (second)
import Data.Foldable (fold, traverse_)
import Data.List (intercalate)
import Data.Set (Set, union, (\\))
import qualified Data.Set as Set

-- logical xor
infixl 6 |+|

-- logical and
infixl 7 |*|

class BooleanRing e where
  zero :: e
  one :: e
  (|*|) :: e -> e -> e
  (|+|) :: e -> e -> e
  inc :: e -> e
  inc e = e |+| one

data Term
  = -- vector space of GF(2) (as in paper) of constants
    -- existance in set implies c{x,y....}, where c = 1
    -- ie, {{"a","b"}, {}} = a|*|b |+| 1
    Const (Set (Set String))
  | -- xa + b
    -- (x `and` a) `xor` b
    -- x not in free(a,b)
    Poly String Term Term
  deriving (Show)

pretty :: Term -> String
pretty (Const c) | Set.null c = "0"
pretty (Const c) = intercalate " + " $ map product (Set.toList c)
  where
    product c | Set.null c = "1"
    product c = fold c
pretty (Poly x a b) = x ++ "(" ++ pretty a ++ ") + " ++ pretty b

poly :: String -> Term -> Term -> Term
poly _ (Const a) e | Set.null a = e
poly x a b = Poly x a b

instance BooleanRing Term where
  zero = Const $ Set.empty
  one = Const $ Set.singleton Set.empty
  Const c |*| Poly x a b = poly x (a |*| Const c) (b |*| Const c)
  Poly x a b |*| Const c = poly x (Const c |*| a) (Const c |*| b)
  Const a |*| Const b = foldr (|+|) zero $ do
    a' <- Set.toList a
    b' <- Set.toList b
    pure $ Const $ Set.singleton $ Set.union a' b'
  Poly x a b |*| Poly x' c d | x == x' = poly x (f' |+| i' |+| o') l
    where
      f' = a |*| c
      o' = a |*| d
      i' = b |*| c
      l = b |*| d
  Poly x a b |*| Poly y c d = f |+| o |+| i |+| l
    where
      f = poly x (poly y (m |*| (p |+| q) |+| n |*| (p |+| q)) zero) zero
        where
          (m, n) = factor y a
          (p, q) = factor x c
      o = poly x (a |*| (m |+| n)) zero
        where
          (m, n) = factor x d
      i = poly y ((m |+| n) |*| c) zero
        where
          (m, n) = factor y b
      l = b |*| d
  Const a |+| Const b = Const $ (a \\ b) `union` (b \\ a)
  Const c |+| Poly x a b = poly x a (Const c |+| b)
  Poly x a b |+| Const c = poly x a (b |+| Const c)
  Poly x a b |+| Poly x' c d | x == x' = poly x (a |+| c) (b |+| d)
  Poly x a b |+| Poly y c d = poly x (poly y e (a |+| g)) (poly y f (b |+| i))
    where
      (e, f) = factor x c
      (g, i) = factor x d

factor :: String -> Term -> (Term, Term)
factor _ (Const c) = (zero, Const c)
factor x (Poly x' a b) | x == x' = (a, b)
factor x (Poly y a b) = (poly y c e, poly y d f)
  where
    (c, d) = factor x a
    (e, f) = factor x b

substitute :: (String, Term) -> Term -> Term
substitute (x, ex) (Poly x' a b) | x == x' = ex |*| a |+| b
substitute (x, ex) (Poly x' a b) = variable x' |*| substitute (x, ex) a |+| substitute (x, ex) b
substitute _ (Const c) = Const c

variable :: String -> Term
variable x = Poly x one zero

constant :: String -> Term
constant x = Const $ Set.singleton (Set.singleton x)

fresh :: StateT Int IO Term
fresh = do
  i <- get
  put (i + 1)
  pure $ variable (show i)

solve' :: Term -> StateT Int IO [(String, Term)]
solve' (Const e) | Set.null e = pure []
solve' (Poly x t1 t2) = do
  θ <- solve' (inc t1 |*| t2)
  u <- fresh
  let apply e = foldr substitute e θ
  pure $ (x, apply $ inc t1 |*| u |+| t2) : θ
solve' (Const c) = fail $ "unification error: " ++ show c

run :: StateT Int IO e -> IO e
run e = evalStateT e 0

solve :: Term -> IO ()
solve e = run (solve' e) >>= traverse_ (\(x, e) -> putStrLn $ x ++ " = " ++ pretty e)

satify :: Term -> IO ()
satify e = solve (inc e)

unify :: Term -> Term -> IO ()
unify e1 e2 = solve (e1 |+| e2)

test :: IO ()
test = unify (variable "x" |*| constant "a") (constant "a")

or' :: Term -> Term -> Term
or' x y = x |+| y |+| x |*| y

all' :: (Foldable t) => t Term -> Term
all' = foldr (|*|) one

any' :: (Foldable t) => t Term -> Term
any' = foldr (or') zero

adder c x y cout s = adder' [c, x, y, cout, s]
  where
    adder' terms = any' $ map (all' . zipWith apply [0 ..]) adderRaw
      where
        apply index '0' = inc $ terms !! index
        apply index '1' = terms !! index
    adderRaw =
      [ "00000",
        "00101",
        "01001",
        "01110",
        "10001",
        "10110",
        "11010",
        "11111"
      ]

testAdder = satify $ adder (constant "x") (constant "y") (constant "z") (variable "Cout") (variable "S")
