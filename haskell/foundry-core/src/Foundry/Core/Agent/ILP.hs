{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // foundry // ilp
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Agent.ILP
Description : Pure Haskell Integer Linear Programming solver
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Pure Haskell ILP solver using Simplex + Branch-and-Bound.

== Dependencies

This module: None (pure Haskell)
Dependents:  Foundry.Core.Agent.Allocation (uses solve)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Agent.ILP
  ( -- * Problem types
    ILPProblem (..)
  , Objective (..)
  , Constraint (..)
  , Relation (..)
  , VarBounds (..)
  
    -- * Solution types
  , ILPSolution (..)
  , SolveResult (..)
  
    -- * Solver
  , solve
  ) where

import Data.List (minimumBy)
import Data.Ord (comparing)

--------------------------------------------------------------------------------
-- PUBLIC TYPES
--------------------------------------------------------------------------------

-- | Optimization direction
data Objective
  = Minimize
  | Maximize
  deriving stock (Eq, Show)

-- | Constraint relation
data Relation
  = LessEq      -- ^ ≤
  | Equal       -- ^ =
  | GreaterEq   -- ^ ≥
  deriving stock (Eq, Show)

-- | Variable bounds
data VarBounds = VarBounds
  { varLower :: !Int   -- ^ Lower bound
  , varUpper :: !Int   -- ^ Upper bound
  }
  deriving stock (Eq, Show)

-- | A linear constraint: Σ coeffs[i] * x[i] `rel` rhs
data Constraint = Constraint
  { constraintCoeffs :: ![Int]    -- ^ Coefficients (sparse would be better)
  , constraintRel    :: !Relation -- ^ ≤, =, or ≥
  , constraintRHS    :: !Int      -- ^ Right-hand side
  }
  deriving stock (Eq, Show)

-- | Integer Linear Programming problem
data ILPProblem = ILPProblem
  { ilpObjective   :: !Objective     -- ^ Minimize or Maximize
  , ilpObjCoeffs   :: ![Int]         -- ^ Objective function coefficients
  , ilpConstraints :: ![Constraint]  -- ^ Linear constraints
  , ilpBounds      :: ![VarBounds]   -- ^ Variable bounds
  , ilpNumVars     :: !Int           -- ^ Number of variables
  }
  deriving stock (Eq, Show)

-- | Solution to ILP
data ILPSolution = ILPSolution
  { solValues   :: ![Int]    -- ^ Variable values
  , solObjValue :: !Int      -- ^ Objective function value
  , solGap      :: !Double   -- ^ Optimality gap (0 = proven optimal)
  }
  deriving stock (Eq, Show)

-- | Result of solving
data SolveResult
  = Optimal !ILPSolution     -- ^ Found proven optimal solution
  | Feasible !ILPSolution    -- ^ Found feasible solution (may not be optimal)
  | Infeasible               -- ^ No feasible solution exists
  | Unbounded                -- ^ Objective unbounded
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- INTERNAL TYPES (Simplex)
--------------------------------------------------------------------------------

-- | Simplex tableau for LP relaxation
-- Uses Rational internally for exact arithmetic
data Tableau = Tableau
  { tabMatrix   :: ![[Rational]]  -- ^ Augmented matrix [A|b]
  , tabObjRow   :: ![Rational]    -- ^ Objective row (negated coeffs)
  , tabBasic    :: ![Int]         -- ^ Basic variable indices
  , tabNumVars  :: !Int           -- ^ Original variable count
  }
  deriving stock (Eq, Show)

-- | LP solution (rational values)
data LPSolution = LPSolution
  { lpValues   :: ![Rational]   -- ^ Variable values
  , lpObjValue :: !Rational     -- ^ Objective value
  }
  deriving stock (Eq, Show)

-- | LP solve result
data LPResult
  = LPOptimal !LPSolution
  | LPInfeasible
  | LPUnbounded
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- SIMPLEX ALGORITHM
--------------------------------------------------------------------------------

-- | Convert ILP to initial Simplex tableau
toTableau :: ILPProblem -> Tableau
toTableau problem = Tableau
  { tabMatrix = matrix
  , tabObjRow = objRow
  , tabBasic = basicVars
  , tabNumVars = n
  }
  where
    n = ilpNumVars problem
    constraints = ilpConstraints problem
    m = length constraints
    
    -- Convert constraints to standard form (all ≤ with slack variables)
    matrix = zipWith mkRow [0..] constraints
    mkRow i c = 
      let coeffs = map fromIntegral (constraintCoeffs c)
          slack = replicate i 0 <> [1] <> replicate (m - i - 1) 0
          rhs = fromIntegral (constraintRHS c)
      in coeffs <> slack <> [rhs]
    
    -- Objective row (for maximization, negate for minimization)
    objCoeffs = map fromIntegral (ilpObjCoeffs problem)
    sign = case ilpObjective problem of
      Maximize -> 1
      Minimize -> -1
    objRow = map (* sign) objCoeffs <> replicate m 0 <> [0]
    
    -- Initial basic variables are slack variables
    basicVars = [n .. n + m - 1]

-- | Run Simplex algorithm on tableau
simplex :: Tableau -> LPResult
simplex tab
  | isOptimal tab = LPOptimal (extractSolution tab)
  | isUnbounded tab = LPUnbounded
  | otherwise = simplex (pivot tab)

-- | Check if tableau is optimal (no positive coeffs in obj row)
isOptimal :: Tableau -> Bool
isOptimal tab = all (<= 0) (init (tabObjRow tab))

-- | Check if problem is unbounded
isUnbounded :: Tableau -> Bool
isUnbounded tab =
  case findPivotCol tab of
    Nothing -> False
    Just col -> all (<= 0) [row !! col | row <- tabMatrix tab]

-- | Find pivot column (most positive obj coeff)
findPivotCol :: Tableau -> Maybe Int
findPivotCol tab =
  let objRow = init (tabObjRow tab)
      indexed = zip [0..] objRow
      positive = filter ((> 0) . snd) indexed
  in case positive of
    [] -> Nothing
    ps -> Just (fst (maximumBy (comparing snd) ps))
  where
    maximumBy :: (a -> a -> Ordering) -> [a] -> a
    maximumBy cmp = foldr1 (\x y -> if cmp x y == GT then x else y)

-- | Find pivot row (minimum ratio test)
findPivotRow :: Tableau -> Int -> Maybe Int
findPivotRow tab col =
  let rows = tabMatrix tab
      ratios = [(i, last row / row !! col) 
               | (i, row) <- zip [0..] rows
               , row !! col > 0]
  in case ratios of
    [] -> Nothing
    rs -> Just (fst (minimumBy (comparing snd) rs))

-- | Perform pivot operation
pivot :: Tableau -> Tableau
pivot tab = case findPivotCol tab of
  Nothing -> tab
  Just col -> case findPivotRow tab col of
    Nothing -> tab
    Just row -> doPivot tab row col

-- | Execute pivot at (row, col)
doPivot :: Tableau -> Int -> Int -> Tableau
doPivot tab pivotRow pivotCol = tab
  { tabMatrix = newMatrix
  , tabObjRow = newObjRow
  , tabBasic = newBasic
  }
  where
    matrix = tabMatrix tab
    pivotElem = (matrix !! pivotRow) !! pivotCol
    
    -- Normalize pivot row
    normalizedPivotRow = map (/ pivotElem) (matrix !! pivotRow)
    
    -- Eliminate pivot column from other rows
    newMatrix = 
      [ if i == pivotRow 
        then normalizedPivotRow
        else eliminateRow (matrix !! i) normalizedPivotRow ((matrix !! i) !! pivotCol)
      | i <- [0 .. length matrix - 1]
      ]
    
    -- Eliminate from objective row
    objCoeff = tabObjRow tab !! pivotCol
    newObjRow = eliminateRow (tabObjRow tab) normalizedPivotRow objCoeff
    
    -- Update basic variables
    newBasic = 
      [ if i == pivotRow then pivotCol else tabBasic tab !! i
      | i <- [0 .. length (tabBasic tab) - 1]
      ]
    
    eliminateRow :: [Rational] -> [Rational] -> Rational -> [Rational]
    eliminateRow row pivRow coeff = zipWith (\a b -> a - coeff * b) row pivRow

-- | Extract solution from optimal tableau
extractSolution :: Tableau -> LPSolution
extractSolution tab = LPSolution
  { lpValues = values
  , lpObjValue = last (tabObjRow tab)
  }
  where
    n = tabNumVars tab
    basic = tabBasic tab
    matrix = tabMatrix tab
    
    values = 
      [ if var `elem` basic
        then last (matrix !! basicIdx var)
        else 0
      | var <- [0 .. n - 1]
      ]
    
    basicIdx :: Int -> Int
    basicIdx var = 
      case filter (\i -> basic !! i == var) [0 .. length basic - 1] of
        (i:_) -> i
        []    -> 0  -- Should not happen for basic vars

--------------------------------------------------------------------------------
-- BRANCH AND BOUND
--------------------------------------------------------------------------------

-- | Check if all values are integral (used by findFractional)
_allIntegral :: [Rational] -> Bool
_allIntegral = all isIntegral
  where
    isIntegral :: Rational -> Bool
    isIntegral r = r == fromInteger (round r)

-- | Find first fractional variable
findFractional :: [Rational] -> Maybe (Int, Rational)
findFractional vals =
  case filter (not . isIntegral . snd) (zip [0..] vals) of
    []    -> Nothing
    (x:_) -> Just x
  where
    isIntegral r = r == fromInteger (round r)

-- | Round rationals to integers
roundSolution :: LPSolution -> ILPSolution
roundSolution lp = ILPSolution
  { solValues = map roundRat (lpValues lp)
  , solObjValue = roundRat (lpObjValue lp)
  , solGap = 0.0
  }
  where
    roundRat :: Rational -> Int
    roundRat r = round (fromRational r :: Double)

-- | Add bound constraint to problem
addBound :: ILPProblem -> Int -> Relation -> Int -> ILPProblem
addBound problem varIdx rel bound = problem
  { ilpConstraints = ilpConstraints problem <> [newConstraint]
  }
  where
    n = ilpNumVars problem
    coeffs = replicate varIdx 0 <> [1] <> replicate (n - varIdx - 1) 0
    newConstraint = Constraint coeffs rel bound

-- | Branch and bound solver
branchAndBound :: ILPProblem -> Maybe ILPSolution -> SolveResult
branchAndBound problem incumbent =
  case simplex (toTableau problem) of
    LPInfeasible -> maybe Infeasible Optimal incumbent
    LPUnbounded -> Unbounded
    LPOptimal lpSol ->
      -- Prune if LP bound worse than incumbent
      case incumbent of
        Just inc | shouldPrune lpSol inc problem -> Optimal inc
        _ -> 
          -- Check integrality
          case findFractional (lpValues lpSol) of
            Nothing -> 
              -- All integral - new incumbent
              let newInc = roundSolution lpSol
              in Optimal newInc
            Just (varIdx, fracVal) ->
              -- Branch on fractional variable
              let floorVal = floor fracVal
                  ceilVal = ceiling fracVal
                  leftProblem = addBound problem varIdx LessEq floorVal
                  rightProblem = addBound problem varIdx GreaterEq ceilVal
                  leftResult = branchAndBound leftProblem incumbent
                  rightResult = branchAndBound rightProblem (bestIncumbent leftResult incumbent)
              in bestResult leftResult rightResult

-- | Check if LP bound is worse than incumbent (pruning)
shouldPrune :: LPSolution -> ILPSolution -> ILPProblem -> Bool
shouldPrune lpSol inc problem =
  case ilpObjective problem of
    Maximize -> lpBound <= incBound
    Minimize -> lpBound >= incBound
  where
    lpBound :: Double
    lpBound = fromRational (lpObjValue lpSol)
    incBound :: Double
    incBound = fromIntegral (solObjValue inc)

-- | Get best incumbent from result
bestIncumbent :: SolveResult -> Maybe ILPSolution -> Maybe ILPSolution
bestIncumbent (Optimal sol) _ = Just sol
bestIncumbent (Feasible sol) _ = Just sol
bestIncumbent _ inc = inc

-- | Get best of two results
bestResult :: SolveResult -> SolveResult -> SolveResult
bestResult (Optimal a) (Optimal b) = Optimal (betterSolution a b)
bestResult (Optimal a) _ = Optimal a
bestResult _ (Optimal b) = Optimal b
bestResult Infeasible r = r
bestResult r Infeasible = r
bestResult r _ = r

-- | Compare two solutions (assuming maximization for now)
betterSolution :: ILPSolution -> ILPSolution -> ILPSolution
betterSolution a b = if solObjValue a >= solObjValue b then a else b

--------------------------------------------------------------------------------
-- PUBLIC API
--------------------------------------------------------------------------------

-- | Solve an ILP problem
--
-- Uses Simplex for LP relaxation, then Branch-and-Bound for integrality.
solve :: ILPProblem -> SolveResult
solve problem
  | ilpNumVars problem <= 0 = Infeasible
  | null (ilpConstraints problem) = Infeasible
  | otherwise = branchAndBound problem Nothing
