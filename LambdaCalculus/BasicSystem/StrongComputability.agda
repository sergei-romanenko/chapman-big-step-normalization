module BasicSystem.StrongComputability where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics
open import BasicSystem.OPEBigStep

SCV : ∀ {Γ α} → Val Γ α → Set
SCV {Γ} {⋆}     (ne n) = Σ (NeNf Γ ⋆) λ m → quotⁿ n ⇓ m × (embNeVal n ≈ embNeNf m)
SCV {Γ} {α ⇒ β} v       = ∀ {B}(f : _≤_ B Γ)(a : Val B α) → SCV a → 
  Σ (Val B β) 
    λ w → (val≤ f v ∙∙ a ⇓ w) × SCV w × (embVal (val≤ f v) ∙ embVal a ≈ embVal w)    

data SCE {Γ : Ctx} : ∀ {Δ} → Env Γ Δ → Set where
  s[] : SCE []
  s<< : ∀ {Δ α}{vs : Env Γ Δ}{v : Val Γ α} →
        SCE vs → SCV v → SCE (v ∷ vs)

helper : ∀ {Θ}{α}{β}{f f' : Val Θ (α ⇒ β)} → f ≡ f' → 
    {a : Val Θ α} →
    Σ (Val Θ β) (λ v → (f' ∙∙ a ⇓ v) × SCV v × (embVal f' ∙ embVal a ≈ embVal v)) →
    Σ (Val Θ β) λ v → (f ∙∙ a ⇓ v) × SCV v × (embVal f ∙ embVal a ≈ embVal v)
helper refl p = p 

helper' : ∀ {Θ}{α}{β}{f f' : Val Θ (α ⇒ β)} → f ≡ f' → 
    {a : Val Θ α}{v : Val Θ β} → f' ∙∙ a ⇓ v → f ∙∙ a ⇓ v
helper' refl p = p 

helper'' : ∀ {Θ}{α}{β}{f f' : Val Θ (α ⇒ β)} → f ≡ f' → 
    {a : Val Θ α}{v : Val Θ β} → 
    embVal f' ∙ embVal a ≈ embVal v → embVal f ∙ embVal a ≈ embVal v
helper'' refl p = p 

scval≤ : ∀ {Γ Δ α}(f : _≤_ Γ Δ)(v : Val Δ α) → SCV v → SCV (val≤ f v)
scval≤ {α = ⋆}     f (ne m) (n , p , q) = 
  neNf≤ f n ,
      quotⁿ⇓map f p ,
          ≈trans (embNeVal∘≤ f m) (≈trans (≈cong[] q ≈≈refl) (≈sym (embNeNf∘≤ f n)))
scval≤ {α = α ⇒ β} f v       sv = λ f' a sa → 
  helper (val≤∘ f' f v) (sv (_●_ f' f) a sa) 

scenv≤ : ∀ {B Γ Δ}(f : _≤_ B Γ)(vs : Env Γ Δ) → 
         SCE vs → SCE (env≤ f vs)
scenv≤ f []         s[]         = s[] 
scenv≤ f (v ∷ vs) (s<< p p') = s<< (scenv≤ f vs p) (scval≤ f v p') 
