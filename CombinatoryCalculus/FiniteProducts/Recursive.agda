module FiniteProducts.Recursive where

open import FiniteProducts.Syntax

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
prⁿ     ⟨∙⟩ x        = prⁿ¹ x
prⁿ¹ x  ⟨∙⟩ y        = prⁿ² x y 
fstⁿ    ⟨∙⟩ prⁿ² x y = x
sndⁿ    ⟨∙⟩ prⁿ² x y = y 

nf : {α : Ty} → Tm α → Nf α
nf K = K0
nf S = S0
nf (t ∙ u) = nf t ⟨∙⟩ nf u
nf void = voidⁿ
nf pr = prⁿ
nf fst = fstⁿ
nf snd = sndⁿ