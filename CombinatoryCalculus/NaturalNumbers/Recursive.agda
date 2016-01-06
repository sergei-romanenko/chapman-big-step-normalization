module NaturalNumbers.Recursive where

open import NaturalNumbers.Utils
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
Suc0    ⟨∙⟩ n       = Suc1 n
R0      ⟨∙⟩ z       = R1 z
R1 z   ⟨∙⟩ f       = R2 z f
R2 z f ⟨∙⟩ Zero0   = z
R2 z f ⟨∙⟩ Suc1 n  = (f ⟨∙⟩ n) ⟨∙⟩ (R2 z f ⟨∙⟩ n)

nf : {α : Ty} → Tm α → Nf α
nf K = K0
nf S = S0
nf (t ∙ u) = nf t ⟨∙⟩ nf u
nf Zero = Zero0
nf Suc  = Suc0
nf R    = R0

sound : ∀ {α}{t u : Tm α} → t ≈ u → nf t ≡ nf u
sound ≈refl        = refl 
sound (≈sym p)     = sym (sound p) 
sound (≈trans p q) = trans (sound p) (sound q) 
sound ≈K          = refl 
sound ≈S          = refl 
sound (≈cong∙ p q)    = cong₂ _⟨∙⟩_ (sound p) (sound q)
sound ≈RZero      = refl 
sound ≈RSuc       = refl 
