module BasicSystem.IdentityEnvironment where
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.Embeddings

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
