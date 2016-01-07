module FiniteProducts.RecursiveNormaliser where

open import FiniteProducts.Syntax
open import FiniteProducts.OPE
open import FiniteProducts.IdentityEnvironment

{-# TERMINATING #-}
mutual
  eval : ∀ {Γ Δ σ} → Tm Δ σ → Env Γ Δ → Val Γ σ
  eval ø        (vs << v) = v
  eval (t [ ts ]) vs        = eval t (evalˢ ts vs)
  eval (ƛ t)     vs        = λv t vs
  eval (t ∙ u)    vs        = eval t vs ∙∙ eval u vs
  eval void       vs        = voidv
  eval < t , u >  vs        = < eval t vs , eval u vs >v
  eval (fst t)    vs        = vfst (eval t vs) 
  eval (snd t)    vs        = vsnd (eval t vs) 

  vfst : ∀ {Γ σ τ} → Val Γ (σ * τ) → Val Γ σ
  vfst < v , w >v = v
  vfst (nev n)    = nev (fstV n)

  vsnd : ∀ {Γ σ τ} → Val Γ (σ * τ) → Val Γ τ
  vsnd < v , w >v = w
  vsnd (nev n)    = nev (sndV n)

  _∙∙_ : ∀ {Γ σ τ} → Val Γ (σ ⇒ τ) → Val Γ σ → Val Γ τ
  λv t vs ∙∙ v = eval t (vs << v)
  nev n   ∙∙ v = nev (appV n v)

  evalˢ : ∀ {Γ Δ Σ} → Sub Δ Σ → Env Γ Δ → Env Γ Σ
  evalˢ (↑ σ)   (vs << v) = vs
  evalˢ (ts < t)  vs        = evalˢ ts vs << eval t vs
  evalˢ ı        vs        = vs
  evalˢ (ts ○ us) vs        = evalˢ ts (evalˢ us vs)

{-# TERMINATING #-}
mutual
  quot : ∀ {Γ σ} → Val Γ σ → Nf Γ σ
  quot {σ = ⋆}     (nev n) = ne (quotⁿ n)
  quot {σ = σ ⇒ τ} f       = λn (quot (vwk σ f ∙∙ nev (varV vZ)))
  quot {σ = One}   _   = voidn
  quot {σ = σ * τ} p   = < quot (vfst p) , quot (vsnd p) >n   

  -- shouldn't quot return voidn for anything of type One?
  -- but then what happens to neutral terms? Aren't there any?

  quotⁿ : ∀ {Γ σ} → NeV Γ σ → NeN Γ σ
  quotⁿ (varV x)   = varN x
  quotⁿ (appV n v) = appN (quotⁿ n) (quot v)
  quotⁿ (fstV n)   = fstN (quotⁿ n) 
  quotⁿ (sndV n)   = sndN (quotⁿ n) 

nf : ∀ {Γ σ} → Tm Γ σ → Nf Γ σ
nf t = quot (eval t vid)
