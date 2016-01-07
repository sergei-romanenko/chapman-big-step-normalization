module FullSystem.IdentityEnvironment where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.Embeddings
open import FullSystem.Conversion
open import FullSystem.OPE
open import FullSystem.OPELemmas

vid : ∀ {Γ} → Env Γ Γ
vid {ε}     = ε
vid {Γ < σ} = emap (skip σ oid) vid << nev (varV vZ)

embvid : ∀ {Γ} → ı {Γ} ≃ embˢ vid
embvid {ε}     = ≃refl 
embvid {Γ < σ} = 
  ≃trans idcomp 
         (cong< (≃trans (≃trans (cong○ (≃trans (≃sym rightidˢ) 
                                               (cong○ embvid lemoid)) 
                                       ≃refl)
                                assoc) 
                        (≃sym (oeemb (skip σ oid) vid)) )
                ≈refl) 
