{-# OPTIONS --no-termination-check #-}

module BasicSystem.RecursiveNormaliser where
open import BasicSystem.Syntax
open import BasicSystem.OPE

mutual
  eval : ∀ {Γ Δ σ} → Tm Δ σ → Env Γ Δ → Val Γ σ
  eval ø        (vs << v) = v
  eval (t [ ts ]) vs        = eval t (evalˢ ts vs)
  eval (ƛ t)     vs        = λv t vs
  eval (t ∙ u)    vs        = eval t vs ∙∙ eval u vs

  _∙∙_ : ∀ {Γ σ τ} → Val Γ (σ ⇒ τ) → Val Γ σ → Val Γ τ
  λv t vs ∙∙ v = eval t (vs << v)
  nev n   ∙∙ v = nev (appV n v)

  evalˢ : ∀ {Γ Δ Σ} → Sub Δ Σ → Env Γ Δ → Env Γ Σ
  evalˢ (↑ σ)   (vs << v) = vs
  evalˢ (ts < t)  vs        = evalˢ ts vs << eval t vs
  evalˢ ı        vs        = vs
  evalˢ (ts ○ us) vs        = evalˢ ts (evalˢ us vs)

mutual
  quot : ∀ {Γ σ} → Val Γ σ → Nf Γ σ
  quot {σ = σ ⇒ τ} f       = λn (quot (vwk σ f ∙∙ nev (varV vZ)))
  quot {σ = ⋆}     (nev n) = ne (quotⁿ n)

  quotⁿ : ∀ {Γ σ} → NeV Γ σ → NeN Γ σ
  quotⁿ (varV x)   = varN x
  quotⁿ (appV n v) = appN (quotⁿ n) (quot v)

open import BasicSystem.IdentityEnvironment

nf : ∀ {Γ σ} → Tm Γ σ → Nf Γ σ
nf t = quot (eval t vid)
