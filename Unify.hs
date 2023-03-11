{-# LANGUAGE NoMonomorphismRestriction #-}

module Unify where

import Data.Foldable (traverse_)
import Data.List (intercalate, sortOn)
import Data.Set (Set, union, (\\))
import qualified Data.Set as Set

-- polynomial of boolean ring
-- represented as sums of products of variables
newtype Polynomial x = Polynomial (Set (Set x))
  deriving (Show)

instance Ord x => Num (Polynomial x) where
  -- 0 is false, 1 is true
  fromInteger n = case n `mod` 2 == 0 of
    True -> Polynomial $ Set.empty
    False -> Polynomial $ Set.singleton Set.empty

  -- logical and
  Polynomial a * Polynomial b = sum $ do
    a' <- Set.toList a
    b' <- Set.toList b
    pure $ Polynomial $ Set.singleton $ Set.union a' b'

  -- logical xor
  Polynomial a + Polynomial b = Polynomial $ (a \\ b) `union` (b \\ a)
  abs = id
  negate = id
  signum _ = 1

inc x = x + 1

factor :: Ord x => x -> Polynomial x -> (Polynomial x, Polynomial x)
factor x (Polynomial e) =
  ( Polynomial $ Set.map (Set.delete x) $ Set.filter (Set.member x) e,
    Polynomial $ Set.filter (Set.notMember x) e
  )

pretty :: (x -> String) -> Polynomial x -> String
pretty _ (Polynomial c) | Set.null c = "0"
pretty f (Polynomial c) = intercalate " + " $ map product (Set.toList c)
  where
    product c | Set.null c = "1"
    product c = intercalate "*" $ map f $ Set.toList c

data Variable
  = Flexible String
  | Constant String
  deriving (Show, Eq, Ord)

variable :: String -> Polynomial Variable
variable x = Polynomial $ Set.singleton $ Set.singleton $ Flexible x

constant :: String -> Polynomial Variable
constant x = Polynomial $ Set.singleton $ Set.singleton $ Constant x

prettyVariable (Flexible x) = x
prettyVariable (Constant x) = x

substitute :: (String, Polynomial Variable) -> Polynomial Variable -> Polynomial Variable
substitute (x, ex) (Polynomial e) = sum (map mul $ Set.toList e)
  where
    mul e = product (map apply $ Set.toList e)
      where
        apply (Flexible x') | x == x' = ex
        apply e = Polynomial $ Set.singleton $ Set.singleton e

freeVariables :: Polynomial Variable -> Set String
freeVariables (Polynomial e) = Set.fromList $ do
  e' <- Set.toList e
  e'' <- Set.toList e'
  case e'' of
    Flexible x -> [x]
    Constant _ -> []

-- solve for a single variable in a problem
-- given a variable to solve for `x` and a problem `e` to solve for
-- return `(e', r)` where `e'` is the reduced problem and `r` is the solution to x
solveStep :: String -> Polynomial Variable -> (Polynomial Variable, Polynomial Variable)
solveStep x e =
  let (t1, t2) = factor (Flexible x) e
   in (inc t1 * t2, inc t1 * variable x + t2)

-- combine a set of problems into a single one
combine problem = inc $ product (map inc problem)

-- given a variable split the problem set into problems with and with it
split :: String -> [Polynomial Variable] -> ([Polynomial Variable], [Polynomial Variable])
split x problem = (filter (Set.member x . freeVariables) problem, filter (Set.notMember x . freeVariables) problem)

-- solve a set of problems (for zero) by choosing the least used variable,
-- then combinating problems that contain that variable and solving for that it
-- returns a substitution in triangluar form but in reverse
solveAllImpl :: MonadFail f => [String] -> [Polynomial Variable] -> f [(String, Polynomial Variable)]
solveAllImpl xs [] = pure []
solveAllImpl [] problem = fail $ "unification error: [" ++ intercalate "," (map (pretty prettyVariable) problem) ++ "]"
solveAllImpl xs problem =
  let (x, (simple, problem')) = head $ sortOn (length . fst . snd) $ map (\x -> (x, split x problem)) xs
      (simple', answer) = solveStep x (combine simple)
   in ((x, answer) :) <$> solveAll (filter (/= x) xs) (simple' : problem')

solveAll :: MonadFail f => [String] -> [Polynomial Variable] -> f [(String, Polynomial Variable)]
solveAll xs problem = solveAllImpl xs (filter (\(Polynomial e) -> not $ Set.null e) problem)

-- rename variables that substitute for themself into new ones
renameAnswers :: Int -> [(String, Polynomial Variable)] -> [(String, Polynomial Variable)]
renameAnswers _ [] = []
renameAnswers i ((x, e) : θ) =
  (x, substitute (x, variable $ "_x" ++ show i) e) : renameAnswers (i + 1) θ

-- given a substitution in reverse triangular form, apply future substitutions
backSubstitute :: [(String, Polynomial Variable)] -> [(String, Polynomial Variable)]
backSubstitute [] = []
backSubstitute ((x, e) : θ) =
  let θ' = backSubstitute θ
   in (x, foldr substitute e θ') : θ'

printAnswers :: [(String, Polynomial Variable)] -> IO ()
printAnswers =
  traverse_ (\(x, e) -> putStrLn $ x ++ " = " ++ pretty prettyVariable e)

solveAllIO e = do
  θ <- solveAll (Set.toList $ foldMap freeVariables e) e
  printAnswers $ backSubstitute $ (renameAnswers 0 θ)

satifyAllIO :: [Polynomial Variable] -> IO ()
satifyAllIO e = solveAllIO (map inc e)

solveIO :: Polynomial Variable -> IO ()
solveIO e = solveAllIO [e]

satifyIO :: Polynomial Variable -> IO ()
satifyIO e = solveIO (inc e)

unifyIO :: Polynomial Variable -> Polynomial Variable -> IO ()
unifyIO e1 e2 = solveIO (e1 + e2)

testBasic :: IO ()
testBasic = unifyIO (variable "x" * constant "a") (constant "a")

testAdder :: IO ()
testAdder = satifyIO $ adder [constant "c", constant "x", constant "y", variable "Cout", variable "S"]
  where
    adder terms = any' $ map (all' . zipWith apply [0 ..]) adderRaw
      where
        apply index '0' = inc $ terms !! index
        apply index '1' = terms !! index
        apply _ _ = error "bad number"
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
    any' = foldr (\x y -> x + y + x * y) 0
    all' = product

testRedundant =
  solveAllIO
    [ or (variable "v3") (variable "v5") + or (variable "v14") (variable "v5"),
      or (variable "v14") (variable "v5") + or (variable "v16") (variable "v5"),
      or (variable "v16") (variable "v5") + or (variable "v18") (variable "v5"),
      or (variable "v18") (variable "v5") + or (variable "v20") (variable "v5"),
      or (variable "v20") (variable "v5") + or (variable "v22") (variable "v5"),
      or (variable "v22") (variable "v5") + or (variable "v24") (variable "v5"),
      or (variable "v24") (variable "v5") + or (variable "v26") (variable "v5"),
      or (variable "v26") (variable "v5") + or (variable "v28") (variable "v5"),
      or (variable "v28") (variable "v5") + or (variable "v30") (variable "v5"),
      or (variable "v30") (variable "v5") + or (variable "v32") (variable "v5"),
      or (variable "v32") (variable "v5") + or (variable "v34") (variable "v5"),
      or (variable "v34") (variable "v5") + or (variable "v36") (variable "v5"),
      or (variable "v36") (variable "v5") + or (variable "v38") (variable "v5"),
      or (variable "v38") (variable "v5") + or (variable "v40") (variable "v5"),
      or (variable "v40") (variable "v5") + or (variable "v42") (variable "v5"),
      variable "v42" + or (variable "v43") (variable "v5"),
      variable "v40" + or (variable "v41") (variable "v5"),
      variable "v38" + or (variable "v39") (variable "v5"),
      variable "v36" + or (variable "v37") (variable "v5"),
      variable "v34" + or (variable "v35") (variable "v5"),
      variable "v32" + or (variable "v33") (variable "v5"),
      variable "v30" + or (variable "v31") (variable "v5"),
      variable "v28" + or (variable "v29") (variable "v5"),
      variable "v26" + or (variable "v27") (variable "v5"),
      variable "v24" + or (variable "v25") (variable "v5"),
      variable "v22" + or (variable "v23") (variable "v5"),
      variable "v20" + or (variable "v21") (variable "v5"),
      variable "v18" + or (variable "v19") (variable "v5"),
      variable "v16" + or (variable "v17") (variable "v5"),
      variable "v14" + or (variable "v15") (variable "v5"),
      variable "v3" + or (variable "v11") (variable "v5")
    ]
  where
    or x y = x + y + x * y

testRigid =
  solveAllIO
    [ constant "A" + or (variable "v6") (variable "v8"),
      (constant "A") * (constant "C") + variable "v20",
      (constant "A") * (constant "B") + variable "v8",
      or (variable "v6") (variable "v8") + or (variable "v18") (variable "v20")
    ]
  where
    or x y = x + y + x * y
