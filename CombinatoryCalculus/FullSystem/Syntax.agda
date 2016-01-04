module FullSystem.Syntax where

-- Types
data Ty : Set where
  ⋆ : Ty
  N : Ty
  One : Ty
  Zero : Ty
  _⇒_  : Ty → Ty → Ty
  _*_ : Ty → Ty → Ty
  _+_  : Ty → Ty → Ty

infixr 50 _⇒_

-- Terms
data Tm : Ty → Set where
  K : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  void : Tm One
  pr   : ∀ {α β} → Tm (α ⇒ β ⇒ (α * β))
  fst  : ∀ {α β} → Tm ((α * β) ⇒ α)
  snd  : ∀ {α β} → Tm ((α * β) ⇒ β)
  NE   : ∀ {α} → Tm (Zero ⇒ α) 
  Inl  : ∀ {α β} → Tm (α ⇒ (α + β))
  Inr  : ∀ {α β} → Tm (β ⇒ (α + β))
  C : ∀ {α β γ} → Tm ((α ⇒ γ) ⇒ (β ⇒ γ) ⇒ (α + β) ⇒ γ)
  zero : Tm N
  suc  : Tm (N ⇒ N)
  R    : ∀ {α} → Tm (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)
 
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
  ≈fst : ∀ {α β}{t : Tm α}{u : Tm β} → fst ∙ (pr ∙ t ∙ u) ≈ t
  ≈snd : ∀ {α β}{t : Tm α}{u : Tm β} → snd ∙ (pr ∙ t ∙ u) ≈ u
  Cl : ∀ {α β γ}{l : Tm (α ⇒ γ)}{r : Tm (β ⇒ γ)}{c : Tm α} → C ∙ l ∙ r ∙ (Inl ∙ c) ≈ l ∙ c
  Cr : ∀ {α β γ}{l : Tm (α ⇒ γ)}{r : Tm (β ⇒ γ)}{c : Tm β} → C ∙ l ∙ r ∙ (Inr ∙ c) ≈ r ∙ c
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
  voidⁿ : Nf One
  prⁿ   : ∀ {α β} → Nf (α ⇒ β ⇒ (α * β))
  prⁿ¹  : ∀ {α β} → Nf α → Nf (β ⇒ (α * β))
  prⁿ²  : ∀ {α β} → Nf α → Nf β → Nf (α * β)
  fstⁿ  : ∀ {α β} → Nf ((α * β) ⇒ α)
  sndⁿ  : ∀ {α β} → Nf ((α * β) ⇒ β)
  NE0  : ∀ {α} → Nf (Zero ⇒ α)
  Inl0  : ∀ {α β} → Nf (α ⇒ (α + β))
  Inl1 : ∀ {α β} → Nf α → Nf (α + β)
  Inr0  : ∀ {α β} → Nf (β ⇒ (α + β))
  Inr1 : ∀ {α β} → Nf β → Nf (α + β)
  C0 : ∀ {α β γ} → Nf ((α ⇒ γ) ⇒ (β ⇒ γ) ⇒ (α + β) ⇒ γ)
  C1 : ∀ {α β γ} → Nf (α ⇒ γ) → Nf ((β ⇒ γ) ⇒ (α + β) ⇒ γ)
  C2 : ∀ {α β γ} → Nf (α ⇒ γ) → Nf (β ⇒ γ) → Nf ((α + β) ⇒ γ)
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
⌜ voidⁿ ⌝ = void
⌜ prⁿ ⌝ = pr 
⌜ prⁿ¹ x ⌝ = pr ∙ ⌜ x ⌝
⌜ prⁿ² x y ⌝ = pr ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ fstⁿ ⌝ = fst
⌜ sndⁿ ⌝ = snd 
⌜ NE0 ⌝ = NE
⌜ Inl1 x ⌝ = Inl ∙ ⌜ x ⌝
⌜ Inl0 ⌝ = Inl
⌜ Inr1 x ⌝ = Inr ∙ ⌜ x ⌝
⌜ Inr0 ⌝ = Inr
⌜ C0 ⌝ = C
⌜ C1 l ⌝ = C ∙ ⌜ l ⌝
⌜ C2 l r ⌝ = C ∙ ⌜ l ⌝ ∙ ⌜ r ⌝
⌜ zeroⁿ ⌝ = zero
⌜ sucⁿ ⌝ = suc
⌜ sucⁿ¹ n ⌝ = suc ∙ ⌜ n ⌝
⌜ Rⁿ ⌝ = R
⌜ Rⁿ¹ z ⌝ = R ∙ ⌜ z ⌝
⌜ Rⁿ² z f ⌝ = R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝
