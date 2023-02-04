{-# LANGUAGE NoMonomorphismRestriction #-}

module Unify where

import Control.Monad.Trans.State
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
    Constant (Set (Set String))
  | -- xa + b
    -- (x `and` a) `xor` b
    -- x not in free(a,b)
    Polynomial String Term Term
  deriving (Show)

pretty :: Term -> String
pretty (Constant c) | Set.null c = "0"
pretty (Constant c) = intercalate " + " $ map product (Set.toList c)
  where
    product c | Set.null c = "1"
    product c = fold c
pretty (Polynomial x a b) = x ++ "(" ++ pretty a ++ ") + " ++ pretty b

polynomial :: String -> Term -> Term -> Term
polynomial _ (Constant a) e | Set.null a = e
polynomial x a b = Polynomial x a b

instance BooleanRing Term where
  zero = Constant $ Set.empty
  one = Constant $ Set.singleton Set.empty
  Constant c |*| Polynomial x a b = polynomial x (a |*| Constant c) (b |*| Constant c)
  Polynomial x a b |*| Constant c = polynomial x (Constant c |*| a) (Constant c |*| b)
  Constant a |*| Constant b = foldr (|+|) zero $ do
    a' <- Set.toList a
    b' <- Set.toList b
    pure $ Constant $ Set.singleton $ Set.union a' b'
  Polynomial x a b |*| Polynomial x' c d | x == x' = polynomial x (f' |+| i' |+| o') l
    where
      f' = a |*| c
      o' = a |*| d
      i' = b |*| c
      l = b |*| d
  Polynomial x a b |*| Polynomial y c d = f |+| o |+| i |+| l
    where
      f = polynomial x (polynomial y (m |*| (p |+| q) |+| n |*| (p |+| q)) zero) zero
        where
          (m, n) = factor y a
          (p, q) = factor x c
      o = polynomial x (a |*| (m |+| n)) zero
        where
          (m, n) = factor x d
      i = polynomial y ((m |+| n) |*| c) zero
        where
          (m, n) = factor y b
      l = b |*| d
  Constant a |+| Constant b = Constant $ (a \\ b) `union` (b \\ a)
  Constant c |+| Polynomial x a b = polynomial x a (Constant c |+| b)
  Polynomial x a b |+| Constant c = polynomial x a (b |+| Constant c)
  Polynomial x a b |+| Polynomial x' c d | x == x' = polynomial x (a |+| c) (b |+| d)
  Polynomial x a b |+| Polynomial y c d = polynomial x (polynomial y (e |+| i) (k |+| f)) (polynomial y (g |+| j) (l |+| h))
    where
      (e, f) = factor y a
      (g, h) = factor y b
      (i, j) = factor x c
      (k, l) = factor x d

factor :: String -> Term -> (Term, Term)
factor _ (Constant c) = (zero, Constant c)
factor x (Polynomial x' a b) | x == x' = (a, b)
factor x (Polynomial y a b) = (polynomial y c e, polynomial y d f)
  where
    (c, d) = factor x a
    (e, f) = factor x b

substitute :: (String, Term) -> Term -> Term
substitute (x, ex) (Polynomial x' a b) | x == x' = ex |*| a |+| b
substitute (x, ex) (Polynomial x' a b) = variable x' |*| substitute (x, ex) a |+| substitute (x, ex) b
substitute _ (Constant c) = Constant c

variable :: String -> Term
variable x = Polynomial x one zero

constant :: String -> Term
constant x = Constant $ Set.singleton (Set.singleton x)

fresh :: StateT Int IO Term
fresh = do
  i <- get
  put (i + 1)
  pure $ variable ("_" ++ show i)

solve' :: Term -> StateT Int IO [(String, Term)]
solve' (Constant e) | Set.null e = pure []
solve' (Polynomial x t1 t2) = do
  θ <- solve' (inc t1 |*| t2)
  u <- fresh
  let apply e = foldr substitute e θ
  pure $ (x, apply $ inc t1 |*| u |+| t2) : θ
solve' (Constant c) = fail $ "unification error: " ++ show c

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

testAdder = satify $ adder (constant "c") (constant "x") (constant "y") (variable "Cout") (variable "S")
