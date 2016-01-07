module NaturalNumbers.RecursiveNormaliser where

open import NaturalNumbers.Syntax
open import NaturalNumbers.OPE
open import NaturalNumbers.IdentityEnvironment

{-# TERMINATING #-}
mutual
  eval : ∀ {Γ Δ σ} → Tm Δ σ → Env Γ Δ → Val Γ σ
  eval ø          (vs << v) = v
  eval (t [ ts ])   vs        = eval t (evalˢ ts vs)
  eval (ƛ t)       vs        = λv t vs
  eval (t ∙ u)      vs        = eval t vs ∙∙ eval u vs
  eval zero         vs        = zerov
  eval (suc t)      vs        = sucv (eval t vs)
  eval (prim z s n) vs        = vprim (eval z vs) (eval s vs) (eval n vs) 

  vprim : ∀ {Γ σ} → Val Γ σ → Val Γ (N ⇒ σ ⇒ σ) → Val Γ N → Val Γ σ
  vprim z f (nev n)  = nev (primV z f n) 
  vprim z f zerov    = z 
  vprim z f (sucv v) = (f ∙∙ v) ∙∙ (vprim z f v) 

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
  quot {σ = ⋆}     (nev n)   = ne⋆ (quotⁿ n)
  quot {σ = σ ⇒ τ} f         = λn (quot (vwk σ f ∙∙ nev (varV vZ)))
  quot {σ = N}     zerov     = zeron 
  quot {σ = N}     (sucv v)  = sucn (quot v) 
  quot {σ = N}     (nev n)   = neN (quotⁿ n)

  quotⁿ : ∀ {Γ σ} → NeV Γ σ → NeN Γ σ
  quotⁿ (varV x)      = varN x
  quotⁿ (appV n v)    = appN (quotⁿ n) (quot v)
  quotⁿ (primV z s n) = primN (quot z) (quot s) (quotⁿ n)

nf : ∀ {Γ σ} → Tm Γ σ → Nf Γ σ
nf t = quot (eval t vid)
