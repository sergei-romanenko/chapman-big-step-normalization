module BasicSystem.IdentityEnvironment where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Embeddings
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas

vid : ∀ {Γ} → Env Γ Γ
vid {[]}     = []
vid {α ∷ Γ} = ne (var zero) ∷ emap (skip α oid) vid

embvid : ∀ {Γ} → ı {Γ} ≃ embˢ vid
embvid {[]}     = ≃refl 
embvid {α ∷ Γ} = 
  ≃trans idcomp 
         (cong< (≃trans (≃trans (cong○ (≃trans (≃sym rightidˢ) 
                                               (cong○ embvid lemoid)) 
                                       ≃refl)
                                assoc) 
                        (≃sym (oeemb (skip α oid) vid)) )
                ≈refl) 
