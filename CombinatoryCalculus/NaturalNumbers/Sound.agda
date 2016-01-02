module NaturalNumbers.Sound where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.Recursive

sound : ∀ {α}{t u : Tm α} → t ≈ u → nf t ≡ nf u
sound ≈refl        = refl 
sound (≈sym p)     = sym (sound p) 
sound (≈trans p q) = trans (sound p) (sound q) 
sound ≈K          = refl 
sound ≈S          = refl 
sound (≈cong∙ p q)    = cong₂ _⟨∙⟩_ (sound p) (sound q)
sound ≈Rzero      = refl 
sound ≈Rsuc       = refl 
