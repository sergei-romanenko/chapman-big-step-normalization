module FiniteProducts.OPERecursive where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.RecursiveNormaliser

-- Unsurprisingly this isn't structurally recursive

{-# TERMINATING #-}
mutual
  evmaplem : ∀ {B Γ Δ σ}(f : OPE B Γ)(t : Tm Δ σ)(vs : Env Γ Δ) → 
             eval t (emap f vs) ≡ vmap f (eval t vs)
  evmaplem f ø        (vs << v) = refl 
  evmaplem f (t [ ts ]) vs        = 
    trans (cong (eval t) (evˢmaplem f ts vs)) (evmaplem f t (evalˢ ts vs)) 
  evmaplem f (ƛ t)      vs        = refl 
  evmaplem f (t ∙ u)    vs        = 
    trans (cong₂ (λ v a → v ∙∙ a) (evmaplem f t vs) (evmaplem f u vs))
           (∙∙maplem f (eval t vs) (eval u vs))
  evmaplem f void       vs        = refl 
  evmaplem f < t , u >  vs        = cong₂ <_,_>v (evmaplem f t vs) (evmaplem f u vs) 
  evmaplem f (fst t)    vs        = trans (cong vfst (evmaplem f t vs)) 
                                           (vfstmaplem f (eval t vs)) 
  evmaplem f (snd t)    vs        = trans (cong vsnd (evmaplem f t vs)) 
                                           (vsndmaplem f (eval t vs)) 

  vfstmaplem : ∀ {B Γ σ τ}(f : OPE B Γ)(v : Val Γ (σ * τ)) →
               vfst (vmap f v) ≡ vmap f (vfst v)
  vfstmaplem f < v , w >v = refl 
  vfstmaplem f (nev n)    = refl 

  vsndmaplem : ∀ {B Γ σ τ}(f : OPE B Γ)(v : Val Γ (σ * τ)) →
               vsnd (vmap f v) ≡ vmap f (vsnd v)
  vsndmaplem f < v , w >v = refl 
  vsndmaplem f (nev n)    = refl 

  ∙∙maplem : ∀ {Γ Δ σ τ}(f : OPE Γ Δ)(v : Val Δ (σ ⇒ τ))(a : Val Δ σ) →
             vmap f v ∙∙ vmap f a ≡ vmap f (v ∙∙ a)
  ∙∙maplem f (λv t vs) a = evmaplem f t (vs << a) 
  ∙∙maplem f (nev n)   a = refl 

  evˢmaplem : ∀ {A B Γ Δ}(f : OPE A B)(ts : Sub Γ Δ)(vs : Env B Γ) →
              evalˢ ts (emap f vs) ≡ emap f (evalˢ ts vs)
  evˢmaplem f (↑ σ)   (vs << v) = refl 
  evˢmaplem f (ts < t)  vs        = 
    cong₂ _<<_ (evˢmaplem f ts vs) (evmaplem f t vs) 
  evˢmaplem f ı        vs        = refl 
  evˢmaplem f (ts ○ us) vs        = 
    trans (cong (evalˢ ts) (evˢmaplem f us vs)) 
           (evˢmaplem f ts (evalˢ us vs))  

{-# TERMINATING #-}
mutual
  qmaplem : ∀ {Γ Δ σ}(f : OPE Γ Δ)(v : Val Δ σ) → 
             quot (vmap f v) ≡ nfmap f (quot v)
  qmaplem {σ = ⋆}     f (nev n) = cong ne (qⁿmaplem f n) 
  qmaplem {σ = σ ⇒ τ} f v       = 
    cong λn 
         (trans (cong (λ v → quot (v ∙∙ nev (varV vZ))) 
                       (compvmap (skip σ oid) f v)) 
                 (trans (trans (cong (λ f → quot (vmap (skip σ f) v ∙∙ nev (varV vZ))) 
                                       (trans (leftid f) (sym (rightid f))))
                                 (cong quot (trans (cong (λ v → v ∙∙ nev (varV vZ))
                                                           (sym (compvmap (keep σ f) (skip σ oid) v)))  
                                                     (∙∙maplem (keep σ f) 
                                                               (vmap (skip σ oid) v) 
                                                               (nev (varV vZ)) ))))
                         (qmaplem (keep σ f) 
                                  (vmap (skip σ oid) v ∙∙ nev (varV vZ))))) 
  qmaplem {σ = One}   f v       = refl 
  qmaplem {σ = σ * τ} f v       = 
    cong₂ <_,_>n (trans (cong quot (vfstmaplem f v)) (qmaplem f (vfst v))) 
                 (trans  (cong quot (vsndmaplem f v)) (qmaplem f (vsnd v))) 

  qⁿmaplem : ∀ {Γ Δ σ}(f : OPE Γ Δ)(n : NeV Δ σ) → 
             quotⁿ (nevmap f n) ≡ nenmap f (quotⁿ n)
  qⁿmaplem f (varV x)   = refl 
  qⁿmaplem f (appV n v) = cong₂ appN (qⁿmaplem f n) (qmaplem f v) 
  qⁿmaplem f (fstV n)   = cong fstN (qⁿmaplem f n) 
  qⁿmaplem f (sndV n)   = cong sndN (qⁿmaplem f n) 
