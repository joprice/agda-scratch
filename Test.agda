
{--

http://agda.readthedocs.io/en/v2.5.3/tools/emacs-mode.html

typecheck with C-c C-l

--}
module Test where

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (suc n) + m = suc (n + m)

  data _even : ℕ → Set where
    ZERO : zero even
    STEP : ∀ {x} → x even → suc (suc x) even

  proof₁ : suc(suc(suc(suc zero))) even
  -- -- start with question mark
  -- proof₁ = ?
  -- -- C-c C-l over ? will provide a hole
  -- proof₁ = {!   !}
  -- proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)
  proof₁ = STEP (STEP ZERO)

  proof₂′ : (A : Set) → A → A
  proof₂′ _ x = x

  proof₂ : ℕ → ℕ
  proof₂ = proof₂′ ℕ
