module BetaEta.Variables where
open import BetaEta.Syntax

data Var : ∀ Γ → Ty Γ → Set where
  vZ : ∀ {Γ σ} → Var (Γ , σ) (σ [ pop σ ]⁺)
  vS : ∀ {Γ σ} → Var Γ σ → (τ : Ty Γ) → Var (Γ , τ) (σ [ pop τ ]⁺)

embˣ : ∀ {Γ σ} → Var Γ σ → Tm Γ σ
embˣ vZ     = top
embˣ (vS x τ) = embˣ x [ pop τ ]