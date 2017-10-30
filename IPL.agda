module IPL where

  data _∧_ (P : Set) (Q : Set) : Set where
    ∧-intro : P → Q → (P ∧ Q)

  -- eliimination rule "and-elimi-1" / "and-elim-left"
  proof₁ : {P Q : Set} → (P ∧ Q) → P
  proof₁ (∧-intro p q) = p

  proof₂ : {P Q : Set} → (P ∧ Q) → Q
  proof₂ (∧-intro p q) = q
