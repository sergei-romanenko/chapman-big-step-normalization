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
  K    : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S    : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_  : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  void : Tm One
  pr   : ∀ {α β} → Tm (α ⇒ β ⇒ (α * β))
  fst  : ∀ {α β} → Tm ((α * β) ⇒ α)
  snd  : ∀ {α β} → Tm ((α * β) ⇒ β)
 
infixl 50 _∙_

-- Definitional Equality
data _≈_ : ∀ {α} → Tm α → Tm α → Set where
  ≈refl  : ∀ {α}{t : Tm α} → t ≈ t
  ≈sym   : ∀ {α}{t t' : Tm α} → t ≈ t' → t' ≈ t
  ≈trans : ∀ {α}{t t' t'' : Tm α} → t ≈ t' → t' ≈ t'' → t ≈ t''
  ≈K    : ∀ {α β}{x : Tm α}{y : Tm β} → K ∙ x ∙ y ≈ x
  ≈S    : ∀ {α β γ}{x : Tm (α ⇒ β ⇒ γ)}{y : Tm (α ⇒ β)}{z : Tm α} →
          S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)
  ≈cong∙ : ∀ {α}{β}{t t' : Tm (α ⇒ β)}{u u' : Tm α} → t ≈ t' → u ≈ u' →
          t ∙ u ≈ t' ∙ u'
  ≈fst  : ∀ {α β}{t : Tm α}{u : Tm β} → fst ∙ (pr ∙ t ∙ u) ≈ t
  ≈snd  : ∀ {α β}{t : Tm α}{u : Tm β} → snd ∙ (pr ∙ t ∙ u) ≈ u

-- Normal forms
data Nf : Ty → Set where
  K0    : ∀ {α β} → Nf (α ⇒ β ⇒ α)
  K1   : ∀ {α β} → Nf α → Nf (β ⇒ α)
  S0    : ∀ {α β γ} → Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1   : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2   : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf (α ⇒ β) → Nf (α ⇒ γ)
  voidⁿ : Nf One
  prⁿ   : ∀ {α β} → Nf (α ⇒ β ⇒ (α * β))
  prⁿ¹  : ∀ {α β} → Nf α → Nf (β ⇒ (α * β))
  prⁿ²  : ∀ {α β} → Nf α → Nf β → Nf (α * β)
  fstⁿ  : ∀ {α β} → Nf ((α * β) ⇒ α)
  sndⁿ  : ∀ {α β} → Nf ((α * β) ⇒ β)

-- Inclusion of normal forms in terms
⌜_⌝ : ∀ {α} → Nf α → Tm α
⌜ K0       ⌝ = K
⌜ K1 x    ⌝ = K ∙ ⌜ x ⌝
⌜ S0       ⌝ = S
⌜ S1 x    ⌝ = S ∙ ⌜ x ⌝
⌜ S2 x y  ⌝ = S ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ voidⁿ    ⌝ = void
⌜ prⁿ      ⌝ = pr 
⌜ prⁿ¹ x   ⌝ = pr ∙ ⌜ x ⌝
⌜ prⁿ² x y ⌝ = pr ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ fstⁿ     ⌝ = fst
⌜ sndⁿ     ⌝ = snd 
