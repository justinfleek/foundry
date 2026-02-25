{- |
Module      : Metxt.Core.Agent.Budget
Description : Linear resource budget tracking
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Budget tracking with linear resource accounting.
-}
module Metxt.Core.Agent.Budget
  ( -- * Types
    Budget (..)
  , BudgetLimit (..)

    -- * Operations
  , mkBudget
  , spendBudget
  , remainingBudget
  , isBudgetExhausted
  ) where

-- | Budget limit in USD cents (to avoid floating point)
newtype BudgetLimit = BudgetLimit {unBudgetLimit :: !Int}
  deriving stock (Eq, Ord, Show)

-- | Current budget state
data Budget = Budget
  { budgetLimit :: !BudgetLimit     -- ^ Maximum allowed spend
  , budgetSpent :: !Int             -- ^ Amount spent (cents)
  }
  deriving stock (Eq, Show)

-- | Create initial budget
mkBudget :: BudgetLimit -> Budget
mkBudget limit = Budget limit 0

-- | Spend from budget (returns Nothing if insufficient)
spendBudget :: Int -> Budget -> Maybe Budget
spendBudget amount budget
  | newSpent <= unBudgetLimit (budgetLimit budget) =
      Just budget {budgetSpent = newSpent}
  | otherwise = Nothing
  where
    newSpent = budgetSpent budget + amount

-- | Get remaining budget
remainingBudget :: Budget -> Int
remainingBudget budget =
  unBudgetLimit (budgetLimit budget) - budgetSpent budget

-- | Check if budget is exhausted
isBudgetExhausted :: Budget -> Bool
isBudgetExhausted budget = remainingBudget budget <= 0
