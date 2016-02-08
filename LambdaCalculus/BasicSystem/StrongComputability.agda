module BasicSystem.StrongComputability where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Embeddings
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics
open import BasicSystem.OPEBigStep

SCV : ∀ {Γ α} → Val Γ α → Set
SCV {Γ} {⋆}     (ne n) = Σ (NeNf Γ ⋆) λ m → quotⁿ n ⇓ m × (embⁿ n ≈ nembⁿ m)
SCV {Γ} {α ⇒ β} v       = ∀ {B}(f : OPE B Γ)(a : Val B α) → SCV a → 
  Σ (Val B β) 
    λ w → (vmap f v ∙∙ a ⇓ w) × SCV w × (emb (vmap f v) ∙ emb a ≈ emb w)    

data SCE {Γ : Ctx} : ∀ {Δ} → Env Γ Δ → Set where
  s[] : SCE []
  s<< : ∀ {Δ α}{vs : Env Γ Δ}{v : Val Γ α} →
        SCE vs → SCV v → SCE (v ∷ vs)

helper : ∀ {Θ}{α}{β}{f f' : Val Θ (α ⇒ β)} → f ≡ f' → 
    {a : Val Θ α} →
    Σ (Val Θ β) (λ v → (f' ∙∙ a ⇓ v) × SCV v × (emb f' ∙ emb a ≈ emb v)) →
    Σ (Val Θ β) λ v → (f ∙∙ a ⇓ v) × SCV v × (emb f ∙ emb a ≈ emb v)
helper refl p = p 

helper' : ∀ {Θ}{α}{β}{f f' : Val Θ (α ⇒ β)} → f ≡ f' → 
    {a : Val Θ α}{v : Val Θ β} → f' ∙∙ a ⇓ v → f ∙∙ a ⇓ v
helper' refl p = p 

helper'' : ∀ {Θ}{α}{β}{f f' : Val Θ (α ⇒ β)} → f ≡ f' → 
    {a : Val Θ α}{v : Val Θ β} → 
    emb f' ∙ emb a ≈ emb v → emb f ∙ emb a ≈ emb v
helper'' refl p = p 

scvmap : ∀ {Γ Δ α}(f : OPE Γ Δ)(v : Val Δ α) → SCV v → SCV (vmap f v)
scvmap {α = ⋆}     f (ne m) (n , p , q) = 
  nenmap f n ,
      quotⁿ⇓map f p ,
          ≈trans (onevemb f m) (≈trans (cong[] q ≃refl) (≈sym (onenemb f n)))
scvmap {α = α ⇒ β} f v       sv = λ f' a sa → 
  helper (compvmap f' f v) (sv (comp f' f) a sa) 

scemap : ∀ {B Γ Δ}(f : OPE B Γ)(vs : Env Γ Δ) → 
         SCE vs → SCE (emap f vs)
scemap f []         s[]         = s[] 
scemap f (v ∷ vs) (s<< p p') = s<< (scemap f vs p) (scvmap f v p') 
