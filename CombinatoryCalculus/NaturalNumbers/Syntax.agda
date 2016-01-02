module NaturalNumbers.Syntax where

-- Types
data Ty : Set where
  ⋆ : Ty
  N : Ty
  _⇒_ : Ty → Ty → Ty

infixr 50 _⇒_

-- Terms
data Tm : Ty → Set where
  K : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  zero : Tm N
  suc  : Tm (N ⇒ N)
  R    : ∀ {α} → Tm (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)

infixl 50 _∙_

-- Definitional Equality
data _≈_ : ∀ {α} → Tm α → Tm α → Set where
  ≈refl  : ∀ {α}{t : Tm α} → t ≈ t
  ≈sym   : ∀ {α}{t t' : Tm α} → t ≈ t' → t' ≈ t
  ≈trans : ∀ {α}{t t' t'' : Tm α} → t ≈ t' → t' ≈ t'' → t ≈ t''
  ≈K     : ∀ {α β}{x : Tm α}{y : Tm β} → K ∙ x ∙ y ≈ x
  ≈S     : ∀ {α β γ}{x : Tm (α ⇒ β ⇒ γ)}{y : Tm (α ⇒ β)}{z : Tm α} →
           S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)
  ≈cong∙     : ∀ {α}{β}{t t' : Tm (α ⇒ β)}{u u' : Tm α} → t ≈ t' → u ≈ u' →
           t ∙ u ≈ t' ∙ u'
  ≈Rzero : ∀ {α}{z : Tm α}{s : Tm (N ⇒ α ⇒ α)} → R ∙ z ∙ s ∙ zero ≈ z
  ≈Rsuc  : ∀ {α}{z : Tm α}{s : Tm (N ⇒ α ⇒ α)}{n : Tm N} → 
           R ∙ z ∙ s ∙ (suc ∙ n) ≈ s ∙ n ∙ (R ∙ z ∙ s ∙ n)

-- Normal forms
data Nf : Ty → Set where
  K0 : ∀ {α β} → Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} → Nf α → Nf (β ⇒ α)
  S0 : ∀ {α β γ} → Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf (α ⇒ β) → Nf (α ⇒ γ)
  zeroⁿ : Nf N
  sucⁿ  : Nf (N ⇒ N)
  sucⁿ¹ : Nf N → Nf N
  Rⁿ    : ∀ {α} → Nf (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)
  Rⁿ¹   : ∀ {α} → Nf α → Nf ((N ⇒ α ⇒ α) ⇒ N ⇒ α)
  Rⁿ²   : ∀ {α} → Nf α → Nf (N ⇒ α ⇒ α) → Nf (N ⇒ α)

-- Inclusion of normal forms in terms
⌜_⌝ : ∀ {α} → Nf α → Tm α
⌜ K0 ⌝ = K
⌜ K1 x ⌝ = K ∙ ⌜ x ⌝
⌜ S0 ⌝ = S
⌜ S1 x ⌝ = S ∙ ⌜ x ⌝
⌜ S2 x y ⌝ = S ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ zeroⁿ ⌝ = zero
⌜ sucⁿ ⌝ = suc
⌜ sucⁿ¹ n ⌝ = suc ∙ ⌜ n ⌝
⌜ Rⁿ ⌝ = R
⌜ Rⁿ¹ z ⌝ = R ∙ ⌜ z ⌝
⌜ Rⁿ² z f ⌝ = R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝
