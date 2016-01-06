module FiniteCoproducts.Recursive where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax

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
NE0 ⟨∙⟩ ()
Inl0 ⟨∙⟩ u = Inl1 u
Inr0 ⟨∙⟩ u = Inr1 u
C0 ⟨∙⟩ u = C1 u
C1 u ⟨∙⟩ v = C2 u v
C2 u v ⟨∙⟩ Inl1 w = u ⟨∙⟩ w
C2 u v ⟨∙⟩ Inr1 w = v ⟨∙⟩ w

⟦_⟧ : ∀ {α} (x : Tm α) → Nf α

⟦ K ⟧ = K0
⟦ S ⟧ = S0
⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧
⟦ NE ⟧ = NE0
⟦ Inl ⟧ = Inl0
⟦ Inr ⟧ = Inr0
⟦ C ⟧ = C0

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
⟦⟧-sound ≈Cl = refl
⟦⟧-sound ≈Cr = refl
