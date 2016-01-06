module FullSystem.Syntax where

import Relation.Binary.EqReasoning as EqReasoning

open import FullSystem.Utils

--
-- Types.
--

infixr 5 _⇒_
infixr 2 _*_
infixr 1 _+_

data Ty : Set where
  ⋆ : Ty
  _⇒_ : Ty → Ty → Ty
  U   : Ty
  _*_ : Ty → Ty → Ty
  Z   : Ty
  _+_ : Ty → Ty → Ty
  N   : Ty

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Ty → Set where
  K : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  Void : Tm U
  Pr   : ∀ {α β} → Tm (α ⇒ β ⇒ (α * β))
  Fst  : ∀ {α β} → Tm ((α * β) ⇒ α)
  Snd  : ∀ {α β} → Tm ((α * β) ⇒ β)
  NE   : ∀ {α} → Tm (Z ⇒ α) 
  Inl  : ∀ {α β} → Tm (α ⇒ (α + β))
  Inr  : ∀ {α β} → Tm (β ⇒ (α + β))
  C : ∀ {α β γ} → Tm ((α ⇒ γ) ⇒ (β ⇒ γ) ⇒ (α + β) ⇒ γ)
  Zero : Tm N
  Suc  : Tm (N ⇒ N)
  R    : ∀ {α} → Tm (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)

--
-- Convertibility.
--

infix 4 _≈_

data _≈_ : ∀ {α} → Tm α → Tm α → Set where
  ≈refl : ∀ {α} {x : Tm α} →
    x ≈ x
  ≈sym : ∀ {α} {x y : Tm α} →
    x ≈ y → y ≈ x
  ≈trans : ∀ {α} {x y z : Tm α} →
    x ≈ y → y ≈ z → x ≈ z
  ≈K : ∀ {α β} {x : Tm α} {y : Tm β} →
    K ∙ x ∙ y ≈ x
  ≈S : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)}{z : Tm α} →
    S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)
  ≈cong∙ : ∀ {α β} {x y : Tm (α ⇒ β)} {x′ y′ : Tm α} →
    x ≈ y → x′ ≈ y′ → x ∙ x′ ≈ y ∙ y′
  ≈Fst : ∀ {α β} {x : Tm α} {y : Tm β} →
    Fst ∙ (Pr ∙ x ∙ y) ≈ x
  ≈Snd : ∀ {α β} {x : Tm α} {y : Tm β} →
    Snd ∙ (Pr ∙ x ∙ y) ≈ y
  ≈Cl : ∀ {α β γ} {x : Tm (α ⇒ γ)} {y : Tm (β ⇒ γ)} {z : Tm α} →
    C ∙ x ∙ y ∙ (Inl ∙ z) ≈ x ∙ z
  ≈Cr : ∀ {α β γ} {x : Tm (α ⇒ γ)} {y : Tm (β ⇒ γ)} {z : Tm β} →
    C ∙ x ∙ y ∙ (Inr ∙ z) ≈ y ∙ z
  ≈Rz : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
    R ∙ x ∙ y ∙ Zero ≈ x
  ≈Rs : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z : Tm N} → 
    R ∙ x ∙ y ∙ (Suc ∙ z) ≈ y ∙ z ∙ (R ∙ x ∙ y ∙ z)

--
-- Setoid reasoning.
--

≈setoid : {α : Ty} → Setoid _ _

≈setoid {α} = record
  { Carrier = Tm α
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans } }

module ≈-Reasoning {α : Ty} = EqReasoning (≈setoid {α})


-- Normal forms
data Nf : Ty → Set where
  K0 : ∀ {α β} → Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} → Nf α → Nf (β ⇒ α)
  S0 : ∀ {α β γ} → Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf (α ⇒ β) → Nf (α ⇒ γ)
  Void0 : Nf U
  Pr0   : ∀ {α β} → Nf (α ⇒ β ⇒ (α * β))
  Pr1  : ∀ {α β} → Nf α → Nf (β ⇒ (α * β))
  Pr2  : ∀ {α β} → Nf α → Nf β → Nf (α * β)
  Fst0  : ∀ {α β} → Nf ((α * β) ⇒ α)
  Snd0  : ∀ {α β} → Nf ((α * β) ⇒ β)
  NE0  : ∀ {α} → Nf (Z ⇒ α)
  Inl0  : ∀ {α β} → Nf (α ⇒ (α + β))
  Inl1 : ∀ {α β} → Nf α → Nf (α + β)
  Inr0  : ∀ {α β} → Nf (β ⇒ (α + β))
  Inr1 : ∀ {α β} → Nf β → Nf (α + β)
  C0 : ∀ {α β γ} → Nf ((α ⇒ γ) ⇒ (β ⇒ γ) ⇒ (α + β) ⇒ γ)
  C1 : ∀ {α β γ} → Nf (α ⇒ γ) → Nf ((β ⇒ γ) ⇒ (α + β) ⇒ γ)
  C2 : ∀ {α β γ} → Nf (α ⇒ γ) → Nf (β ⇒ γ) → Nf ((α + β) ⇒ γ)
  Zero0 : Nf N
  Suc0  : Nf (N ⇒ N)
  Suc1 : Nf N → Nf N
  R0    : ∀ {α} → Nf (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)
  R1   : ∀ {α} → Nf α → Nf ((N ⇒ α ⇒ α) ⇒ N ⇒ α)
  R2   : ∀ {α} → Nf α → Nf (N ⇒ α ⇒ α) → Nf (N ⇒ α)

-- Inclusion of normal forms in terms
⌜_⌝ : ∀ {α} → Nf α → Tm α
⌜ K0 ⌝ = K
⌜ K1 x ⌝ = K ∙ ⌜ x ⌝
⌜ S0 ⌝ = S
⌜ S1 x ⌝ = S ∙ ⌜ x ⌝
⌜ S2 x y ⌝ = S ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ Void0 ⌝ = Void
⌜ Pr0 ⌝ = Pr 
⌜ Pr1 x ⌝ = Pr ∙ ⌜ x ⌝
⌜ Pr2 x y ⌝ = Pr ∙ ⌜ x ⌝ ∙ ⌜ y ⌝
⌜ Fst0 ⌝ = Fst
⌜ Snd0 ⌝ = Snd 
⌜ NE0 ⌝ = NE
⌜ Inl1 x ⌝ = Inl ∙ ⌜ x ⌝
⌜ Inl0 ⌝ = Inl
⌜ Inr1 x ⌝ = Inr ∙ ⌜ x ⌝
⌜ Inr0 ⌝ = Inr
⌜ C0 ⌝ = C
⌜ C1 l ⌝ = C ∙ ⌜ l ⌝
⌜ C2 l r ⌝ = C ∙ ⌜ l ⌝ ∙ ⌜ r ⌝
⌜ Zero0 ⌝ = Zero
⌜ Suc0 ⌝ = Suc
⌜ Suc1 n ⌝ = Suc ∙ ⌜ n ⌝
⌜ R0 ⌝ = R
⌜ R1 z ⌝ = R ∙ ⌜ z ⌝
⌜ R2 z f ⌝ = R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝
