module NaturalNumbers.Recursive where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax

--
-- Recursive normalizer.
--

infixl 5 _⟨∙⟩_

{-# TERMINATING #-}

_⟨∙⟩_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α) → Nf β

K0 ⟨∙⟩ u = K1 u
K1 u ⟨∙⟩ v = u
S0 ⟨∙⟩ u = S1 u
S1 u ⟨∙⟩ v = S2 u v
S2 u v ⟨∙⟩ w = (u ⟨∙⟩ w) ⟨∙⟩ (v ⟨∙⟩ w)
Suc0 ⟨∙⟩ u = Suc1 u
R0 ⟨∙⟩ u = R1 u
R1 u ⟨∙⟩ v = R2 u v
R2 u v ⟨∙⟩ Zero0   = u
R2 u v ⟨∙⟩ Suc1 w  = (v ⟨∙⟩ w) ⟨∙⟩ (R2 u v ⟨∙⟩ w)

⟦_⟧ : ∀ {α} (x : Tm α) → Nf α

⟦ K ⟧ = K0
⟦ S ⟧ = S0
⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧
⟦ Zero ⟧ = Zero0
⟦ Suc ⟧ = Suc0
⟦ R ⟧ = R0

--
-- The following "proof" is correct on condition that _⟨∙⟩_ is total.
-- But Agda's termination checker is unable to prove this fact. :-(
--

⟦⟧-sound : ∀ {α} {x y : Tm α} → x ≈ y → ⟦ x ⟧ ≡ ⟦ y ⟧

⟦⟧-sound ≈refl = refl
⟦⟧-sound (≈sym y≈x) =
  sym (⟦⟧-sound y≈x)
⟦⟧-sound (≈trans x≈y x≈z) =
  trans (⟦⟧-sound x≈y) (⟦⟧-sound x≈z)
⟦⟧-sound ≈K = refl
⟦⟧-sound ≈S = refl
⟦⟧-sound (≈cong∙ x≈x′ y≈y′) =
  cong₂ _⟨∙⟩_ (⟦⟧-sound x≈x′) (⟦⟧-sound y≈y′)
⟦⟧-sound ≈Rz = refl
⟦⟧-sound ≈Rs = refl
