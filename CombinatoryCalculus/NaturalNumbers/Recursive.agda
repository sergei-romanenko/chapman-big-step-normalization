module NaturalNumbers.Recursive where

open import NaturalNumbers.Syntax

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
sucⁿ    ⟨∙⟩ n       = sucⁿ¹ n
Rⁿ      ⟨∙⟩ z       = Rⁿ¹ z
Rⁿ¹ z   ⟨∙⟩ f       = Rⁿ² z f
Rⁿ² z f ⟨∙⟩ zeroⁿ   = z
Rⁿ² z f ⟨∙⟩ sucⁿ¹ n  = (f ⟨∙⟩ n) ⟨∙⟩ (Rⁿ² z f ⟨∙⟩ n)

nf : {α : Ty} → Tm α → Nf α
nf K = K0
nf S = S0
nf (t ∙ u) = nf t ⟨∙⟩ nf u
nf zero = zeroⁿ
nf suc  = sucⁿ
nf R    = Rⁿ