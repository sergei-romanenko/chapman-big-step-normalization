module FullSystem.Sound where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.Recursive

sound : ∀ {σ}{t u : Tm σ} → t ≈ u → nf t ≡ nf u
sound ≈refl        = refl 
sound (≈sym p)     = sym (sound p) 
sound (≈trans p q) = trans (sound p) (sound q) 
sound ≈K          = refl 
sound ≈S          = refl 
sound (≈∙-cong p q)    = cong₂ _∙∙_ (sound p) (sound q)
sound ≈fst        = refl
sound ≈snd        = refl 
sound Cl          = refl 
sound Cr          = refl 
sound ≈Rzero      = refl 
sound ≈Rsuc       = refl 
