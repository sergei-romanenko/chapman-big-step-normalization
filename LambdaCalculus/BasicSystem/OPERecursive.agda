module BasicSystem.OPERecursive where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.RecursiveNormaliser

-- Unsurprisingly this isn't structurally recursive

{-# TERMINATING #-}
mutual
  evmaplem : ∀ {B Γ Δ α}(f : OPE B Γ)(t : Tm Δ α)(vs : Env Γ Δ) → 
             eval t (emap f vs) ≡ vmap f (eval t vs)
  evmaplem f ø        (v ∷ vs) = refl 
  evmaplem f (t [ ts ]) vs        = 
    trans (cong (eval t) (evˢmaplem f ts vs)) (evmaplem f t (evalˢ ts vs)) 
  evmaplem f (ƛ t)     vs        = refl 
  evmaplem f (t ∙ u)    vs        = 
    trans (cong₂ (λ v a → v ∙∙ a) (evmaplem f t vs) (evmaplem f u vs))
           (∙∙maplem f (eval t vs) (eval u vs))
           

  ∙∙maplem : ∀ {Γ Δ α β}(f : OPE Γ Δ)(v : Val Δ (α ⇒ β))(a : Val Δ α) →
             vmap f v ∙∙ vmap f a ≡ vmap f (v ∙∙ a)
  ∙∙maplem f (lam t vs) a = evmaplem f t (a ∷ vs) 
  ∙∙maplem f (ne n)   a = refl 

  evˢmaplem : ∀ {A B Γ Δ}(f : OPE A B)(ts : Sub Γ Δ)(vs : Env B Γ) →
              evalˢ ts (emap f vs) ≡ emap f (evalˢ ts vs)
  evˢmaplem f ↑   (v ∷ vs) = refl 
  evˢmaplem f (t ∷ ts)  vs        = 
    cong₂ _∷_ (evmaplem f t vs) (evˢmaplem f ts vs) 
  evˢmaplem f ı        vs        = refl 
  evˢmaplem f (ts ○ us) vs        = 
    trans (cong (evalˢ ts) (evˢmaplem f us vs)) 
           (evˢmaplem f ts (evalˢ us vs))  

{-# TERMINATING #-}
mutual
  qmaplem : ∀ {Γ Δ α}(f : OPE Γ Δ)(v : Val Δ α) → 
             quot (vmap f v) ≡ nfmap f (quot v)
  qmaplem {α = ⋆}     f (ne n) = cong ne (qⁿmaplem f n) 
  qmaplem {α = α ⇒ β} f v       = 
    cong lam 
         (trans (cong (λ v → quot (v ∙∙ ne (var zero))) 
                       (compvmap (skip α oid) f v)) 
                 (trans (trans (cong (λ f → quot (vmap (skip α f) v ∙∙ ne (var zero))) 
                                       (trans (leftid f) (sym (rightid f))))
                                 (cong quot (trans (cong (λ v → v ∙∙ ne (var zero))
                                                           (sym (compvmap (keep α f) (skip α oid) v)))  
                                                     (∙∙maplem (keep α f) 
                                                               (vmap (skip α oid) v) 
                                                               (ne (var zero)) ))))
                         (qmaplem (keep α f) 
                                  (vmap (skip α oid) v ∙∙ ne (var zero))))) 

  qⁿmaplem : ∀ {Γ Δ α}(f : OPE Γ Δ)(n : NeVal Δ α) → 
             quotⁿ (nevmap f n) ≡ nenmap f (quotⁿ n)
  qⁿmaplem f (var x)   = refl 
  qⁿmaplem f (app n v) = cong₂ app (qⁿmaplem f n) (qmaplem f v) 
