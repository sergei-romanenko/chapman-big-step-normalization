module NaturalNumbers.IdentityEnvironment where
open import NaturalNumbers.Syntax
open import NaturalNumbers.Conversion
open import NaturalNumbers.OPE
open import NaturalNumbers.OPELemmas
open import NaturalNumbers.Embeddings

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
