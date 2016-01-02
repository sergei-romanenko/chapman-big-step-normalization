module FiniteCoproducts.Recursive where

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
NEⁿ     ⟨∙⟩ ()
inlⁿ    ⟨∙⟩ x       = inlⁿ¹ x
inrⁿ    ⟨∙⟩ x       = inrⁿ¹ x
Cⁿ      ⟨∙⟩ l       = Cⁿ¹ l
Cⁿ¹ l   ⟨∙⟩ r       = Cⁿ² l r
Cⁿ² l r ⟨∙⟩ inlⁿ¹ x  = l ⟨∙⟩ x
Cⁿ² l r ⟨∙⟩ inrⁿ¹ x  = r ⟨∙⟩ x

nf : {α : Ty} → Tm α → Nf α
nf K       = K0
nf S       = S0
nf (t ∙ u) = nf t ⟨∙⟩ nf u
nf NE      = NEⁿ
nf inl     = inlⁿ
nf inr     = inrⁿ
nf C       = Cⁿ