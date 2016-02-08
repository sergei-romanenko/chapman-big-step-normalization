module BasicSystem.BigStepSemantics where

open import BasicSystem.Syntax
open import BasicSystem.OPE

mutual
  data eval_&_⇓_ : ∀ {Γ Δ α} → Tm Δ α → Env Γ Δ → Val Γ α → Set where
    rlam  : ∀ {Γ Δ α β}{t : Tm (α ∷ Δ) β}{vs : Env Γ Δ} →
            eval ƛ t & vs ⇓ lam t vs
    rvar  : ∀ {Γ Δ α}{vs : Env Γ Δ}{v : Val Γ α} → 
            eval ø & (v ∷ vs) ⇓ v
    rsubs : ∀ {B Γ Δ α}{t : Tm Δ α}{ts : Sub Γ Δ}{vs : Env B Γ}{ws v} →
            evalˢ ts & vs ⇓ ws → eval t & ws ⇓ v → eval t [ ts ] & vs ⇓ v
    rapp  : ∀ {Γ Δ α β}{t : Tm Δ (α ⇒ β)}{u : Tm Δ α}{vs : Env Γ Δ}
            {f : Val Γ (α ⇒ β)}{a : Val Γ α}{v : Val Γ β} →
            eval t & vs ⇓ f → eval u & vs ⇓ a → f ∙∙ a ⇓ v →
            eval t ∙ u & vs ⇓ v

  data _∙∙_⇓_ : ∀ {Γ α β} → 
                Val Γ (α ⇒ β) → Val Γ α → Val Γ β → Set where
    r∙lam : ∀ {Γ Δ α β}{t : Tm (α ∷ Δ) β}{vs : Env Γ Δ}{a : Val Γ α}{v} →
            eval t & a ∷ vs ⇓ v → lam t vs ∙∙ a ⇓ v
    r∙ne  : ∀ {Γ α β}{n : NeVal Γ (α ⇒ β)}{v : Val Γ α} →
            ne n ∙∙ v ⇓ ne (app n v)

  data evalˢ_&_⇓_ : ∀ {Γ Δ Σ} → 
                    Sub Δ Σ → Env Γ Δ → Env Γ Σ → Set where
    rˢ↑  : ∀ {Γ Δ α}{vs : Env Γ Δ}{v : Val Γ α} → 
             evalˢ ↑ & v ∷ vs ⇓ vs
    rˢcons : ∀ {Γ Δ Σ α}{ts : Sub Δ Σ}{t : Tm Δ α}{vs : Env Γ Δ}{ws v} →
             evalˢ ts & vs ⇓ ws → eval t & vs ⇓ v → 
              evalˢ (t ∷ ts) & vs ⇓ (v ∷ ws)
    rˢid   : ∀ {Γ Δ}{vs : Env Γ Δ} → evalˢ ı & vs ⇓ vs
    rˢcomp : ∀ {A B Γ Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Env A B}{ws}
                    {xs} → evalˢ us & vs ⇓ ws →
                    evalˢ ts & ws ⇓ xs → evalˢ ts ○ us & vs ⇓ xs

mutual
  data quot_⇓_ : ∀ {Γ α} → Val Γ α → Nf Γ α → Set where
    qarr : ∀ {Γ α β}{f : Val Γ (α ⇒ β)}{v : Val (α ∷ Γ) β}{n} →
           vwk α f ∙∙ ne (var zero) ⇓ v →  quot v ⇓ n → quot f ⇓ lam n
    qbase : ∀ {Γ}{m : NeVal Γ ⋆}{n} → quotⁿ m ⇓ n → quot ne m ⇓ ne n

  data quotⁿ_⇓_ : ∀ {Γ α} → NeVal Γ α → NeNf Γ α → Set where
    qⁿvar : ∀ {Γ α}{x : Var Γ α} → quotⁿ var x ⇓ var x
    qⁿapp : ∀ {Γ α β}{m : NeVal Γ (α ⇒ β)}{v}{n}{n'} →
            quotⁿ m ⇓ n → quot v ⇓ n' → quotⁿ app m v ⇓ app n n'

open import BasicSystem.IdentityEnvironment

data nf_⇓_ {Γ : Ctx}{α : Ty} : Tm Γ α → Nf Γ α → Set where
  norm⇓ : ∀ {t v n} → eval t & vid ⇓ v → quot v ⇓ n → nf t ⇓ n
