module BasicSystem.OPEBigStep where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics

mutual
  eval⇓map : ∀ {B Γ Δ α}(f : OPE B Γ)
             {t : Tm Δ α}{vs : Env Γ Δ}{v : Val Γ α} →
             eval t & vs ⇓ v → eval t & emap f vs ⇓ vmap f v
  eval⇓map f rlam            = rlam 
  eval⇓map f rvar            = rvar 
  eval⇓map f (rsubs p p')    = rsubs (evalˢ⇓map f p) (eval⇓map f p') 
  eval⇓map f (rapp p p' p'') = 
    rapp (eval⇓map f p) (eval⇓map f p') (∙∙⇓map f p'') 

  ∙∙⇓map : ∀ {Γ Δ α β}(f : OPE Γ Δ)
           {v : Val Δ (α ⇒ β)}{a : Val Δ α}{v' : Val Δ β} →
           v ∙∙ a ⇓ v' → vmap f v ∙∙ vmap f a ⇓ vmap f v'
  ∙∙⇓map f (r∙lam p) = r∙lam (eval⇓map f p) 
  ∙∙⇓map f r∙ne      = r∙ne 

  evalˢ⇓map : ∀ {A B Γ Δ}(f : OPE A B)
              {ts : Sub Γ Δ}{vs : Env B Γ}{ws : Env B Δ} →
              evalˢ ts & vs ⇓ ws → evalˢ ts & emap f vs ⇓ emap f ws
  evalˢ⇓map f rˢ↑         = rˢ↑ 
  evalˢ⇓map f (rˢcons p p') = rˢcons (evalˢ⇓map f p) (eval⇓map f p') 
  evalˢ⇓map f rˢid          = rˢid 
  evalˢ⇓map f (rˢcomp p p') = rˢcomp (evalˢ⇓map f p) (evalˢ⇓map f p')

mutual
  quot⇓map : ∀ {Γ Δ α}(f : OPE Γ Δ) →
              {v : Val Δ α}{n : Nf Δ α} →
              quot v ⇓ n → quot vmap f v ⇓ nfmap f n
  quot⇓map {α = α ⇒ β} f (qarr {f = v} p p') with ∙∙⇓map (keep _ f) p
  ... | p'' with vmap (keep α f) (vmap (skip α oid) v) | quotlemma α f v
  ... | ._ | refl =
    qarr (vmap (skip α oid) (vmap f v) ∙∙ ne (var zero) ⇓ vmap (keep α f) _
               ∋ p'')
         (quot vmap (keep α f) _ ⇓ nfmap (keep α f) _
               ∋ quot⇓map (keep _ f) p') 
  quot⇓map f (qbase p)   = qbase (quotⁿ⇓map f p) 

  quotⁿ⇓map : ∀ {Γ Δ α}(f : OPE Γ Δ) →
              {n : NeVal Δ α}{n' : NeNf Δ α} →
              quotⁿ n ⇓ n' → quotⁿ nevmap f n ⇓ nenmap f n'
  quotⁿ⇓map f qⁿvar        = qⁿvar 
  quotⁿ⇓map f (qⁿapp p p') = qⁿapp (quotⁿ⇓map f p) (quot⇓map f p') 
