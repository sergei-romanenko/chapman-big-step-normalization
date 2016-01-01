module FiniteProducts.Syntax where

-- Types
data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty
  One : Ty
  _*_ : Ty → Ty → Ty

infixr 50 _⇒_

-- Terms
data Tm : Ty → Set where
  K    : ∀ {σ τ} → Tm (σ ⇒ τ ⇒ σ)
  S    : ∀ {σ τ ρ} → Tm ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  _∙_  : ∀ {σ τ} → Tm (σ ⇒ τ) → Tm σ → Tm τ
  void : Tm One
  pr   : ∀ {σ τ} → Tm (σ ⇒ τ ⇒ (σ * τ))
  fst  : ∀ {σ τ} → Tm ((σ * τ) ⇒ σ)
  snd  : ∀ {σ τ} → Tm ((σ * τ) ⇒ τ)
 
infixl 50 _∙_

-- Definitional Equality
data _≈_ : ∀ {σ} → Tm σ → Tm σ → Set where
  ≈refl  : ∀ {σ}{t : Tm σ} → t ≈ t
  ≈sym   : ∀ {σ}{t t' : Tm σ} → t ≈ t' → t' ≈ t
  ≈trans : ∀ {σ}{t t' t'' : Tm σ} → t ≈ t' → t' ≈ t'' → t ≈ t''
  ≈K    : ∀ {σ τ}{x : Tm σ}{y : Tm τ} → K ∙ x ∙ y ≈ x
  ≈S    : ∀ {σ τ ρ}{x : Tm (σ ⇒ τ ⇒ ρ)}{y : Tm (σ ⇒ τ)}{z : Tm σ} →
          S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)
  ≈∙-cong    : ∀ {σ}{τ}{t t' : Tm (σ ⇒ τ)}{u u' : Tm σ} → t ≈ t' → u ≈ u' →
          t ∙ u ≈ t' ∙ u'
  ≈fst  : ∀ {σ τ}{t : Tm σ}{u : Tm τ} → fst ∙ (pr ∙ t ∙ u) ≈ t
  ≈snd  : ∀ {σ τ}{t : Tm σ}{u : Tm τ} → snd ∙ (pr ∙ t ∙ u) ≈ u

-- Normal forms
data Nf : Ty → Set where
  Kⁿ    : ∀ {σ τ} → Nf (σ ⇒ τ ⇒ σ)
  Kⁿ¹   : ∀ {σ τ} → Nf σ → Nf (τ ⇒ σ)
  Sⁿ    : ∀ {σ τ ρ} → Nf ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ¹   : ∀ {σ τ ρ} → Nf (σ ⇒ τ ⇒ ρ) → Nf ((σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ²   : ∀ {σ τ ρ} → Nf (σ ⇒ τ ⇒ ρ) → Nf (σ ⇒ τ) → Nf (σ ⇒ ρ)
  voidⁿ : Nf One
  prⁿ   : ∀ {σ τ} → Nf (σ ⇒ τ ⇒ (σ * τ))
  prⁿ¹  : ∀ {σ τ} → Nf σ → Nf (τ ⇒ (σ * τ))
  prⁿ²  : ∀ {σ τ} → Nf σ → Nf τ → Nf (σ * τ)
  fstⁿ  : ∀ {σ τ} → Nf ((σ * τ) ⇒ σ)
  sndⁿ  : ∀ {σ τ} → Nf ((σ * τ) ⇒ τ)

-- Inclusion of normal forms in terms
⌜_⌝ : ∀ {σ} → Nf σ → Tm σ
⌜ Kⁿ       ⌝ = K
⌜ Kⁿ¹ x    ⌝ = K ∙ ⌜ x ⌝
⌜ Sⁿ       ⌝ = S
⌜ Sⁿ¹ x    ⌝ = S ∙ ⌜ x ⌝
⌜ Sⁿ² x y  ⌝ = S ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ voidⁿ    ⌝ = void
⌜ prⁿ      ⌝ = pr 
⌜ prⁿ¹ x   ⌝ = pr ∙ ⌜ x ⌝
⌜ prⁿ² x y ⌝ = pr ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ fstⁿ     ⌝ = fst
⌜ sndⁿ     ⌝ = snd 
