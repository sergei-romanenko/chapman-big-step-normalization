module FullSystem.Recursive where

open import FullSystem.Utils
open import FullSystem.Syntax

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
Pr0     ⟨∙⟩ x        = Pr1 x
Pr1 x  ⟨∙⟩ y        = Pr2 x y 
Fst0    ⟨∙⟩ Pr2 x y = x
Snd0    ⟨∙⟩ Pr2 x y = y 
NE0     ⟨∙⟩ ()
Inl0    ⟨∙⟩ x       = Inl1 x
Inr0    ⟨∙⟩ x       = Inr1 x
C0      ⟨∙⟩ l       = C1 l
C1 l   ⟨∙⟩ r       = C2 l r
C2 l r ⟨∙⟩ Inl1 x  = l ⟨∙⟩ x
C2 l r ⟨∙⟩ Inr1 x  = r ⟨∙⟩ x
sucⁿ    ⟨∙⟩ n       = sucⁿ¹ n
Rⁿ      ⟨∙⟩ z       = Rⁿ¹ z
Rⁿ¹ z   ⟨∙⟩ f       = Rⁿ² z f
Rⁿ² z f ⟨∙⟩ zeroⁿ   = z
Rⁿ² z f ⟨∙⟩ sucⁿ¹ n  = (f ⟨∙⟩ n) ⟨∙⟩ (Rⁿ² z f ⟨∙⟩ n)

nf : {α : Ty} → Tm α → Nf α
nf K = K0
nf S = S0
nf (t ∙ u) = nf t ⟨∙⟩ nf u
nf Void = Void0
nf Pr = Pr0
nf Fst = Fst0
nf Snd = Snd0
nf NE      = NE0
nf Inl     = Inl0
nf Inr     = Inr0
nf C       = C0
nf zero = zeroⁿ
nf suc  = sucⁿ
nf R    = Rⁿ

sound : ∀ {α}{t u : Tm α} → t ≈ u → nf t ≡ nf u
sound ≈refl        = refl 
sound (≈sym p)     = sym (sound p) 
sound (≈trans p q) = trans (sound p) (sound q) 
sound ≈K          = refl 
sound ≈S          = refl 
sound (≈cong∙ p q)    = cong₂ _⟨∙⟩_ (sound p) (sound q)
sound ≈Fst        = refl
sound ≈Snd        = refl 
sound Cl          = refl 
sound Cr          = refl 
sound ≈Rzero      = refl 
sound ≈Rsuc       = refl 
