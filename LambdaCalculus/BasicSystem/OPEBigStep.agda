module BasicSystem.OPEBigStep where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics

mutual
  eval⇓map : ∀ {B Γ Δ α}(f : _≤_ B Γ)
             {t : Tm Δ α}{vs : Env Γ Δ}{v : Val Γ α} →
             eval t & vs ⇓ v → eval t & env≤ f vs ⇓ val≤ f v
  eval⇓map f rlam            = rlam 
  eval⇓map f rvar            = rvar 
  eval⇓map f (rsubs p p')    = rsubs (evalˢ⇓map f p) (eval⇓map f p') 
  eval⇓map f (rapp p p' p'') = 
    rapp (eval⇓map f p) (eval⇓map f p') (∙∙⇓map f p'') 

  ∙∙⇓map : ∀ {Γ Δ α β}(f : _≤_ Γ Δ)
           {v : Val Δ (α ⇒ β)}{a : Val Δ α}{v' : Val Δ β} →
           v ∙∙ a ⇓ v' → val≤ f v ∙∙ val≤ f a ⇓ val≤ f v'
  ∙∙⇓map f (r∙lam p) = r∙lam (eval⇓map f p) 
  ∙∙⇓map f r∙ne      = r∙ne 

  evalˢ⇓map : ∀ {A B Γ Δ}(f : _≤_ A B)
              {ts : Sub Γ Δ}{vs : Env B Γ}{ws : Env B Δ} →
              evalˢ ts & vs ⇓ ws → evalˢ ts & env≤ f vs ⇓ env≤ f ws
  evalˢ⇓map f rˢ↑         = rˢ↑ 
  evalˢ⇓map f (rˢcons p p') = rˢcons (evalˢ⇓map f p) (eval⇓map f p') 
  evalˢ⇓map f rˢid          = rˢid 
  evalˢ⇓map f (rˢcomp p p') = rˢcomp (evalˢ⇓map f p) (evalˢ⇓map f p')

mutual
  postulate
    quot⇓map : ∀ {Γ Δ α}(f : _≤_ Γ Δ) →
                {v : Val Δ α}{n : Nf Δ α} →
                quot v ⇓ n → quot val≤ f v ⇓ nf≤ f n
  {-quot⇓map {α = α ⇒ β} f (qarr {f = v} p p') with ∙∙⇓map (≤lift f) p
  ... | p'' with val≤ (≤lift {?} f) (val≤ (≤weak ≤id) v) | wk∘val≤ α f v
  ... | ._ | refl =
    qarr (val≤ (≤weak α ≤id) (val≤ f v) ∙∙ ne (var zero) ⇓ val≤ (≤lift α f) _
               ∋ p'')
         (quot val≤ (≤lift α f) _ ⇓ nf≤ (≤lift α f) _
               ∋ quot⇓map (≤lift _ f) p')
  quot⇓map f (qbase p)   = qbase (quotⁿ⇓map f p) -}

  quotⁿ⇓map : ∀ {Γ Δ α}(f : _≤_ Γ Δ) →
              {n : NeVal Δ α}{n' : NeNf Δ α} →
              quotⁿ n ⇓ n' → quotⁿ neVal≤ f n ⇓ neNf≤ f n'
  quotⁿ⇓map f qⁿvar        = qⁿvar 
  quotⁿ⇓map f (qⁿapp p p') = qⁿapp (quotⁿ⇓map f p) (quot⇓map f p') 
