module BasicSystem.IdentityEnvironment where
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.Embeddings

vid : ∀ {Γ} → Env Γ Γ
vid {ε}     = ε
vid {Γ < σ} = emap (skip σ oid) vid << nev (varV vZ)

embvid : ∀ {Γ} → id {Γ} ≃ˢ embˢ vid
embvid {ε}     = reflˢ 
embvid {Γ < σ} = 
  transˢ idcomp 
         (cong< (transˢ (transˢ (cong○ (transˢ (symˢ rightidˢ) 
                                               (cong○ embvid lemoid)) 
                                       reflˢ)
                                assoc) 
                        (symˢ (oeemb (skip σ oid) vid)) )
                ≈refl) 
