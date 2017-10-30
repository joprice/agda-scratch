module HoleFilling where

data Bool : Set where
  false : Bool
  true : Bool

∧ : Bool → Bool → Bool
-- 1. type check with C-c C-l
-- 2. C-c C-, to show list of goals
-- 3. C-c C-c to show case prompt
-- 4. enter name of a goal from the step 2
∧ false false = false
∧ true false = false
∧ false true = false
∧ true true = true
