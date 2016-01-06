module BasicSystem.Syntax where

import Relation.Binary.EqReasoning as EqReasoning

open import BasicSystem.Utils

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Ty → Set where
  K : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β

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

--
-- Normal forms.
-- 

data Nf : Ty → Set where
  K0 : ∀ {α β} → Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} → Nf α → Nf (β ⇒ α)
  S0 : ∀ {α β γ} → Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} → Nf (α ⇒ β ⇒ γ) → Nf (α ⇒ β) → Nf (α ⇒ γ)

--
-- Inclusion of normal forms in terms.
--

⌜_⌝ : ∀ {α} → Nf α → Tm α
⌜ K0 ⌝ = K
⌜ K1 u ⌝ = K ∙ ⌜ u ⌝
⌜ S0 ⌝ = S
⌜ S1 u ⌝ = S ∙ ⌜ u ⌝
⌜ S2 u v ⌝ = S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝
