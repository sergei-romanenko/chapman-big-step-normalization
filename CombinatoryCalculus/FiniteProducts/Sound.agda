module FiniteProducts.Sound where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.Recursive

sound : ∀ {σ}{t u : Tm σ} → t ≈ u → nf t ≡ nf u
sound ≈refl        = refl 
sound (≈sym p)     = sym (sound p) 
sound (≈trans p q) = trans (sound p) (sound q) 
sound ≈K          = refl 
sound ≈S          = refl 
sound (≈∙-cong p q)    = cong₂ _∙∙_ (sound p) (sound q)
sound ≈fst        = refl
sound ≈snd        = refl 
