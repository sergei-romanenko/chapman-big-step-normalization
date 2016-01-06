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
Suc0    ⟨∙⟩ n       = Suc1 n
R0      ⟨∙⟩ z       = R1 z
R1 z   ⟨∙⟩ f       = R2 z f
R2 z f ⟨∙⟩ Zero0   = z
R2 z f ⟨∙⟩ Suc1 n  = (f ⟨∙⟩ n) ⟨∙⟩ (R2 z f ⟨∙⟩ n)

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
sound ≈Fst        = refl
sound ≈Snd        = refl 
sound ≈Cl         = refl 
sound ≈Cr         = refl 
sound ≈Rz         = refl 
sound ≈Rs       = refl 
