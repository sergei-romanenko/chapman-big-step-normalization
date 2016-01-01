module NaturalNumbers.Syntax where

-- Types
data Ty : Set where
  ⋆ : Ty
  N : Ty
  _⇒_ : Ty → Ty → Ty

infixr 50 _⇒_

-- Terms
data Tm : Ty → Set where
  K    : ∀ {σ τ} → Tm (σ ⇒ τ ⇒ σ)
  S    : ∀ {σ τ ρ} → Tm ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  _∙_  : ∀ {σ τ} → Tm (σ ⇒ τ) → Tm σ → Tm τ
  zero : Tm N
  suc  : Tm (N ⇒ N)
  R    : ∀ {σ} → Tm (σ ⇒ (N ⇒ σ ⇒ σ) ⇒ N ⇒ σ)

infixl 50 _∙_

-- Definitional Equality
data _≈_ : ∀ {σ} → Tm σ → Tm σ → Set where
  ≈refl   : ∀ {σ}{t : Tm σ} → t ≈ t
  ≈sym    : ∀ {σ}{t t' : Tm σ} → t ≈ t' → t' ≈ t
  ≈trans  : ∀ {σ}{t t' t'' : Tm σ} → t ≈ t' → t' ≈ t'' → t ≈ t''
  ≈K     : ∀ {σ τ}{x : Tm σ}{y : Tm τ} → K ∙ x ∙ y ≈ x
  ≈S     : ∀ {σ τ ρ}{x : Tm (σ ⇒ τ ⇒ ρ)}{y : Tm (σ ⇒ τ)}{z : Tm σ} →
           S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)
  ≈∙-cong     : ∀ {σ}{τ}{t t' : Tm (σ ⇒ τ)}{u u' : Tm σ} → t ≈ t' → u ≈ u' →
           t ∙ u ≈ t' ∙ u'
  ≈Rzero : ∀ {σ}{z : Tm σ}{s : Tm (N ⇒ σ ⇒ σ)} → R ∙ z ∙ s ∙ zero ≈ z
  ≈Rsuc  : ∀ {σ}{z : Tm σ}{s : Tm (N ⇒ σ ⇒ σ)}{n : Tm N} → 
           R ∙ z ∙ s ∙ (suc ∙ n) ≈ s ∙ n ∙ (R ∙ z ∙ s ∙ n)

-- Normal forms
data Nf : Ty → Set where
  Kⁿ    : ∀ {σ τ} → Nf (σ ⇒ τ ⇒ σ)
  Kⁿ¹   : ∀ {σ τ} → Nf σ → Nf (τ ⇒ σ)
  Sⁿ    : ∀ {σ τ ρ} → Nf ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ¹   : ∀ {σ τ ρ} → Nf (σ ⇒ τ ⇒ ρ) → Nf ((σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ²   : ∀ {σ τ ρ} → Nf (σ ⇒ τ ⇒ ρ) → Nf (σ ⇒ τ) → Nf (σ ⇒ ρ)
  zeroⁿ : Nf N
  sucⁿ  : Nf (N ⇒ N)
  sucⁿ¹ : Nf N → Nf N
  Rⁿ    : ∀ {σ} → Nf (σ ⇒ (N ⇒ σ ⇒ σ) ⇒ N ⇒ σ)
  Rⁿ¹   : ∀ {σ} → Nf σ → Nf ((N ⇒ σ ⇒ σ) ⇒ N ⇒ σ)
  Rⁿ²   : ∀ {σ} → Nf σ → Nf (N ⇒ σ ⇒ σ) → Nf (N ⇒ σ)

-- Inclusion of normal forms in terms
⌜_⌝ : ∀ {σ} → Nf σ → Tm σ
⌜ Kⁿ      ⌝ = K
⌜ Kⁿ¹ x   ⌝ = K ∙ ⌜ x ⌝
⌜ Sⁿ      ⌝ = S
⌜ Sⁿ¹ x   ⌝ = S ∙ ⌜ x ⌝
⌜ Sⁿ² x y ⌝ = S ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ zeroⁿ   ⌝ = zero
⌜ sucⁿ    ⌝ = suc
⌜ sucⁿ¹ n ⌝ = suc ∙ ⌜ n ⌝
⌜ Rⁿ      ⌝ = R
⌜ Rⁿ¹ z   ⌝ = R ∙ ⌜ z ⌝
⌜ Rⁿ² z f ⌝ = R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝
