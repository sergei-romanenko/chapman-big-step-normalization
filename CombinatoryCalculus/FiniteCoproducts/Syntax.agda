module FiniteCoproducts.Syntax where

-- Types
data Ty : Set where
  ⋆    : Ty
  _⇒_  : Ty → Ty → Ty
  Zero : Ty
  _+_  : Ty → Ty → Ty

infixr 50 _⇒_

-- Terms
data Tm : Ty → Set where
  K   : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  NE  : ∀ {α} → Tm (Zero ⇒ α) 
  inl : ∀ {α β} → Tm (α ⇒ (α + β))
  inr : ∀ {α β} → Tm (β ⇒ (α + β))
  C   : ∀ {α β γ} → Tm ((α ⇒ γ) ⇒ (β ⇒ γ) ⇒ (α + β) ⇒ γ)

infixl 50 _∙_

-- Definitional Equality
data _≈_ : ∀ {α} → Tm α → Tm α → Set where
  ≈refl  : ∀ {α}{t : Tm α} → t ≈ t
  ≈sym   : ∀ {α}{t t' : Tm α} → t ≈ t' → t' ≈ t
  ≈trans : ∀ {α}{t t' t'' : Tm α} → t ≈ t' → t' ≈ t'' → t ≈ t''
  ≈K : ∀ {α β}{x : Tm α}{y : Tm β} → K ∙ x ∙ y ≈ x
  ≈S : ∀ {α β γ}{x : Tm (α ⇒ β ⇒ γ)}{y : Tm (α ⇒ β)}{z : Tm α} →
          S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)
  ≈cong∙ : ∀ {α}{β}{t t' : Tm (α ⇒ β)}{u u' : Tm α} → t ≈ t' → u ≈ u' →
          t ∙ u ≈ t' ∙ u'
  Cl : ∀ {α β γ}{l : Tm (α ⇒ γ)}{r : Tm (β ⇒ γ)}{c : Tm α} → C ∙ l ∙ r ∙ (inl ∙ c) ≈ l ∙ c
  Cr : ∀ {α β γ}{l : Tm (α ⇒ γ)}{r : Tm (β ⇒ γ)}{c : Tm β} → C ∙ l ∙ r ∙ (inr ∙ c) ≈ r ∙ c
  
-- Normal forms
data Nf : Ty → Set where
  K0 : ∀ {α β} → Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} → Nf α → Nf (β ⇒ α)
  S0 : ∀ {α β γ} → Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf (α ⇒ β) → Nf (α ⇒ γ)
  NEⁿ  : ∀ {α} → Nf (Zero ⇒ α)
  inlⁿ  : ∀ {α β} → Nf (α ⇒ (α + β))
  inlⁿ¹ : ∀ {α β} → Nf α → Nf (α + β)
  inrⁿ  : ∀ {α β} → Nf (β ⇒ (α + β))
  inrⁿ¹ : ∀ {α β} → Nf β → Nf (α + β)
  Cⁿ : ∀ {α β γ} → Nf ((α ⇒ γ) ⇒ (β ⇒ γ) ⇒ (α + β) ⇒ γ)
  Cⁿ¹ : ∀ {α β γ} → Nf (α ⇒ γ) → Nf ((β ⇒ γ) ⇒ (α + β) ⇒ γ)
  Cⁿ² : ∀ {α β γ} → Nf (α ⇒ γ) → Nf (β ⇒ γ) → Nf ((α + β) ⇒ γ)

-- Inclusion of normal forms in terms
⌜_⌝ : ∀ {α} → Nf α → Tm α
⌜ K0 ⌝ = K
⌜ K1 x ⌝ = K ∙ ⌜ x ⌝
⌜ S0 ⌝ = S
⌜ S1 x ⌝ = S ∙ ⌜ x ⌝
⌜ S2 x y ⌝ = S ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ NEⁿ ⌝ = NE
⌜ inlⁿ¹ x ⌝ = inl ∙ ⌜ x ⌝
⌜ inlⁿ ⌝ = inl
⌜ inrⁿ¹ x ⌝ = inr ∙ ⌜ x ⌝
⌜ inrⁿ ⌝ = inr
⌜ Cⁿ ⌝ = C
⌜ Cⁿ¹ l ⌝ = C ∙ ⌜ l ⌝
⌜ Cⁿ² l r ⌝ = C ∙ ⌜ l ⌝ ∙ ⌜ r ⌝
