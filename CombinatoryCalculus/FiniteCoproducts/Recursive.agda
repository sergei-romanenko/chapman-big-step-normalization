module FiniteCoproducts.Recursive where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax

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
NE0 ⟨∙⟩ ()
Inl0 ⟨∙⟩ x = Inl1 x
Inr0 ⟨∙⟩ x = Inr1 x
C0 ⟨∙⟩ l = C1 l
C1 l ⟨∙⟩ r = C2 l r
C2 l r ⟨∙⟩ Inl1 x = l ⟨∙⟩ x
C2 l r ⟨∙⟩ Inr1 x = r ⟨∙⟩ x

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
⟦⟧-sound Cl = refl
⟦⟧-sound Cr = refl
