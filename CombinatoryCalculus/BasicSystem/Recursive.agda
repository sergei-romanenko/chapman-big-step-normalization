module BasicSystem.Recursive where

open import BasicSystem.Utils
open import BasicSystem.Syntax

--
-- Recursive normaliser.
--

infixl 5 _⟨∙⟩_

{-# TERMINATING #-}

_⟨∙⟩_ : ∀ {α β} → Nf (α ⇒ β) → Nf α → Nf β

K0 ⟨∙⟩ x = K1 x
K1 x ⟨∙⟩ y = x
S0 ⟨∙⟩ x = S1 x
S1 x ⟨∙⟩ y = S2 x y
S2 x y ⟨∙⟩ z = (x ⟨∙⟩ z) ⟨∙⟩ (y ⟨∙⟩ z)

⟦_⟧ : ∀ {α} (x : Tm α) → Nf α

⟦ K ⟧ = K0
⟦ S ⟧ = S0
⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧

--
-- The following "proof" is correct on condition that _⟨∙⟩_ is total.
-- But Agda's termination checker is unable to prove this fact. :-(
--

⟦⟧-sound : ∀ {α}{x y : Tm α} → x ≈ y → ⟦ x ⟧ ≡ ⟦ y ⟧

⟦⟧-sound ≈refl = refl
⟦⟧-sound (≈sym y≈x) =
  sym (⟦⟧-sound y≈x)
⟦⟧-sound (≈trans x≈y x≈z) =
  trans (⟦⟧-sound x≈y) (⟦⟧-sound x≈z)
⟦⟧-sound ≈K = refl
⟦⟧-sound ≈S = refl
⟦⟧-sound (≈cong∙ x≈x′ y≈y′) =
  cong₂ _⟨∙⟩_ (⟦⟧-sound x≈x′) (⟦⟧-sound y≈y′)
