{-# LANGUAGE NoMonomorphismRestriction #-}

module Unify where

import Control.Monad.Trans.State
import Data.Foldable (traverse_)
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

-- vector space of GF(2) (as in paper) of constants
-- existance in set implies c{x,y....}, where c = 1
-- ie, {{"a","b"}, {}} = a|*|b |+| 1
newtype Space x = Space (Set (Set x))
  deriving (Show)

instance Ord x => BooleanRing (Space x) where
  zero = Space $ Set.empty
  one = Space $ Set.singleton Set.empty
  Space a |*| Space b = foldr (|+|) zero $ do
    a' <- Set.toList a
    b' <- Set.toList b
    pure $ Space $ Set.singleton $ Set.union a' b'
  Space a |+| Space b = Space $ (a \\ b) `union` (b \\ a)

factor :: Ord x => x -> Space x -> (Space x, Space x)
factor x (Space e) =
  ( Space $ Set.map (Set.delete x) $ Set.filter (Set.member x) e,
    Space $ Set.filter (Set.notMember x) e
  )

pretty :: (x -> String) -> Space x -> String
pretty _ (Space c) | Set.null c = "0"
pretty f (Space c) = intercalate " + " $ map product (Set.toList c)
  where
    product c | Set.null c = "1"
    product c = intercalate "*" $ map f $ Set.toList c

data Variable
  = Flexible String
  | Constant String
  deriving (Show, Eq, Ord)

variable x = Space $ Set.singleton $ Set.singleton $ Flexible x

constant x = Space $ Set.singleton $ Set.singleton $ Constant x

prettyVariable (Flexible x) = x
prettyVariable (Constant x) = x

substitute :: (String, Space Variable) -> Space Variable -> Space Variable
substitute (x, ex) (Space e) = foldr (|+|) zero (map mul $ Set.toList e)
  where
    mul e = foldr (|*|) one (map apply $ Set.toList e)
      where
        apply (Flexible x') | x == x' = ex
        apply e = Space $ Set.singleton $ Set.singleton e

freeVariables :: Space Variable -> Set String
freeVariables (Space e) = Set.fromList $ do
  e' <- Set.toList e
  e'' <- Set.toList e'
  case e'' of
    Flexible x -> [x]
    Constant _ -> []

fresh :: StateT Int IO (Space Variable)
fresh = do
  i <- get
  put (i + 1)
  pure $ variable ("x" ++ show i)

run :: StateT Int IO e -> IO e
run e = evalStateT e 0

solveFor :: [String] -> Space Variable -> StateT Int IO [(String, Space Variable)]
solveFor _ (Space e) | Set.null e = pure []
solveFor (x : xs) e = do
  let (t1, t2) = factor (Flexible x) e
  θ <- solveFor xs (inc t1 |*| t2)
  u <- fresh
  let apply e = foldr substitute e θ
  pure $ (x, apply $ inc t1 |*| u |+| t2) : θ
solveFor [] e = fail $ "unification error " ++ pretty prettyVariable e

solve :: Space Variable -> IO ()
solve e = do
  θ <- run (solveFor (Set.toList $ freeVariables e) e)
  traverse_ (\(x, e) -> putStrLn $ x ++ " = " ++ pretty prettyVariable e) θ

satify :: Space Variable -> IO ()
satify e = solve (inc e)

unify :: Space Variable -> Space Variable -> IO ()
unify e1 e2 = solve (e1 |+| e2)

test :: IO ()
test = unify (variable "x" |*| constant "a") (constant "a")

all' = foldr (|*|) one

any' = foldr (\x y -> x |+| y |+| x |*| y) zero

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
