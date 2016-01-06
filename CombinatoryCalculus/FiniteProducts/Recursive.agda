module FiniteProducts.Recursive where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax

--
-- Recursive normaliser.
--

infixl 5 _⟨∙⟩_

{-# TERMINATING #-}

_⟨∙⟩_ : ∀ {α β} → Nf (α ⇒ β) → Nf α → Nf β
K0 ⟨∙⟩ u = K1 u
K1 u ⟨∙⟩ v = u
S0 ⟨∙⟩ u = S1 u
S1 u ⟨∙⟩ v = S2 u v
S2 u v ⟨∙⟩ w = (u ⟨∙⟩ w) ⟨∙⟩ (v ⟨∙⟩ w)
Pr0 ⟨∙⟩ u = Pr1 u
Pr1 u ⟨∙⟩ v = Pr2 u v 
Fst0 ⟨∙⟩ Pr2 u v = u
Snd0 ⟨∙⟩ Pr2 u v = v 

⟦_⟧ : ∀ {α} (x : Tm α) → Nf α

⟦ K ⟧ = K0
⟦ S ⟧ = S0
⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧
⟦ Void ⟧ = Void0
⟦ Pr ⟧ = Pr0
⟦ Fst ⟧ = Fst0
⟦ Snd ⟧ = Snd0

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
⟦⟧-sound ≈Fst = refl
⟦⟧-sound ≈Snd = refl
