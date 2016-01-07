module FiniteProducts.IdentityEnvironment where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.Embeddings
open import FiniteProducts.Conversion
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas

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
