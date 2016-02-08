module BasicSystem.RecursiveNormaliser where

open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.IdentityEnvironment

{-# TERMINATING #-}
mutual
  eval : ∀ {Γ Δ α} → Tm Δ α → Env Γ Δ → Val Γ α
  eval ø        (v ∷ vs) = v
  eval (t [ ts ]) vs        = eval t (evalˢ ts vs)
  eval (ƛ t)     vs        = lam t vs
  eval (t ∙ u)    vs        = eval t vs ∙∙ eval u vs

  _∙∙_ : ∀ {Γ α β} → Val Γ (α ⇒ β) → Val Γ α → Val Γ β
  lam t vs ∙∙ v = eval t (v ∷ vs)
  ne n   ∙∙ v = ne (app n v)

  evalˢ : ∀ {Γ Δ Σ} → Sub Δ Σ → Env Γ Δ → Env Γ Σ
  evalˢ ↑ (v ∷ vs) = vs
  evalˢ (t ∷ ts)  vs        = eval t vs ∷ evalˢ ts vs
  evalˢ ı        vs        = vs
  evalˢ (ts ○ us) vs        = evalˢ ts (evalˢ us vs)

{-# TERMINATING #-}
mutual
  quot : ∀ {Γ α} → Val Γ α → Nf Γ α
  quot {α = α ⇒ β} f       = lam (quot (vwk α f ∙∙ ne (var zero)))
  quot {α = ⋆}     (ne n) = ne (quotⁿ n)

  quotⁿ : ∀ {Γ α} → NeVal Γ α → NeNf Γ α
  quotⁿ (var x)   = var x
  quotⁿ (app n v) = app (quotⁿ n) (quot v)

nf : ∀ {Γ α} → Tm Γ α → Nf Γ α
nf t = quot (eval t vid)
