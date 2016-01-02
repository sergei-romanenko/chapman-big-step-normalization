module FullSystem.Recursive where

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
prⁿ     ⟨∙⟩ x        = prⁿ¹ x
prⁿ¹ x  ⟨∙⟩ y        = prⁿ² x y 
fstⁿ    ⟨∙⟩ prⁿ² x y = x
sndⁿ    ⟨∙⟩ prⁿ² x y = y 
NEⁿ     ⟨∙⟩ ()
inlⁿ    ⟨∙⟩ x       = inlⁿ¹ x
inrⁿ    ⟨∙⟩ x       = inrⁿ¹ x
Cⁿ      ⟨∙⟩ l       = Cⁿ¹ l
Cⁿ¹ l   ⟨∙⟩ r       = Cⁿ² l r
Cⁿ² l r ⟨∙⟩ inlⁿ¹ x  = l ⟨∙⟩ x
Cⁿ² l r ⟨∙⟩ inrⁿ¹ x  = r ⟨∙⟩ x
sucⁿ    ⟨∙⟩ n       = sucⁿ¹ n
Rⁿ      ⟨∙⟩ z       = Rⁿ¹ z
Rⁿ¹ z   ⟨∙⟩ f       = Rⁿ² z f
Rⁿ² z f ⟨∙⟩ zeroⁿ   = z
Rⁿ² z f ⟨∙⟩ sucⁿ¹ n  = (f ⟨∙⟩ n) ⟨∙⟩ (Rⁿ² z f ⟨∙⟩ n)

nf : {α : Ty} → Tm α → Nf α
nf K = K0
nf S = S0
nf (t ∙ u) = nf t ⟨∙⟩ nf u
nf void = voidⁿ
nf pr = prⁿ
nf fst = fstⁿ
nf snd = sndⁿ
nf NE      = NEⁿ
nf inl     = inlⁿ
nf inr     = inrⁿ
nf C       = Cⁿ
nf zero = zeroⁿ
nf suc  = sucⁿ
nf R    = Rⁿ