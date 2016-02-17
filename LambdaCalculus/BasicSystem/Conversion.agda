module BasicSystem.Conversion where

import Relation.Binary.EqReasoning as EqReasoning

open import BasicSystem.Utils
open import BasicSystem.Syntax

--
-- Convertibility.
--

infix 4 _≈_ _≈≈_

mutual

  -- t₁ ≈ t₂

  data _≈_  : ∀ {α Γ} (t₁ t₂ : Tm Γ α) → Set where
    ≈refl : ∀ {α Γ} {t : Tm Γ α} →
      t ≈ t
    ≈sym : ∀ {α Γ} {t₁ t₂ : Tm Γ α} →
      t₁ ≈ t₂ → t₂ ≈ t₁
    ≈trans : ∀ {α Γ} {t₁ t₂ t₃ : Tm Γ α} →
      t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
    ≈cong∙ : ∀ {α β Γ} {f₁ f₂ : Tm Γ (α ⇒ β)} {t₁ t₂ : Tm Γ α} →
      f₁ ≈ f₂ → t₁ ≈ t₂ → f₁ ∙ t₁ ≈ f₂ ∙ t₂
    ≈cong[] : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α } {σ₁ σ₂ : Sub Γ Δ} →
      t₁ ≈ t₂ → σ₁ ≈≈ σ₂ → t₁ [ σ₁ ] ≈ t₂ [ σ₂ ]
    ≈congƛ : ∀ {α β Γ} {t₁ t₂ : Tm (α ∷ Γ) β} →
      t₁ ≈ t₂ → (ƛ t₁) ≈ (ƛ t₂)
    ≈ø[∷] : ∀ {α Γ Δ} {t : Tm Γ α } {σ : Sub Γ Δ} →
      ø [ t ∷ σ ] ≈ t
    ≈[ı] : ∀ {α Γ} {t : Tm Γ α} →
      t [ ı ] ≈ t
    ≈[○] : ∀ {α Γ Δ Γ′} {t : Tm Δ α} {σ : Sub Γ Δ} {σ′ : Sub Γ′ Γ} →
      t [ σ ○ σ′ ] ≈ t [ σ ] [ σ′ ]
    ≈ƛ[] : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} →
      (ƛ t) [ σ ] ≈ (ƛ t [ ø ∷ (σ ○ ↑) ])
    ≈∙[] : ∀ {α β Γ Δ} {f : Tm Δ (α ⇒ β)} {t : Tm Δ α} {σ : Sub Γ Δ} →
      (f ∙ t) [ σ ] ≈ f [ σ ] ∙ t [ σ ]
    ≈βσ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} {t′ : Tm Γ α} →
      (ƛ t) [ σ ] ∙ t′ ≈ t [ t′ ∷ σ ]
    ≈η : ∀ {α β Γ} {t : Tm Γ (α ⇒ β)} →
      t ≈ (ƛ (t [ ↑ ] ∙ ø))

  -- σ₁ ≈≈ σ₂

  data _≈≈_ : ∀ {Γ Δ} (σ₁ σ₂ : Sub Γ Δ) → Set where
    ≈≈refl : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      σ ≈≈ σ
    ≈≈sym : ∀ {Γ Δ} {σ₁ σ₂ : Sub Γ Δ} →
      σ₁ ≈≈ σ₂ → σ₂ ≈≈ σ₁
    ≈≈trans : ∀ {Γ Δ} {σ₁ σ₂ σ₃ : Sub Γ Δ} →
      σ₁ ≈≈ σ₂ → σ₂ ≈≈ σ₃ → σ₁ ≈≈ σ₃
    ≈≈cong○ : ∀ {Γ Δ Γ′} {σ₁ σ₂ : Sub Δ Γ} {τ₁ τ₂ : Sub Γ′ Δ} →
      σ₁ ≈≈ σ₂ → τ₁ ≈≈ τ₂ → σ₁ ○ τ₁ ≈≈ σ₂ ○ τ₂
    ≈≈cong∷ : ∀ {α Γ Δ} {t₁ t₂ : Tm Δ α} {σ₁ σ₂ : Sub Δ Γ} →
      t₁ ≈ t₂ → σ₁ ≈≈ σ₂ → t₁ ∷ σ₁ ≈≈ t₂ ∷ σ₂
    ≈≈assoc : ∀ {Γ Δ Δ′ Γ′} {σ₁ : Sub Δ Γ} {σ₂ : Sub Δ′ Δ} {σ₃ : Sub Γ′ Δ′} →
      (σ₁ ○ σ₂) ○ σ₃ ≈≈ σ₁ ○ (σ₂ ○ σ₃)
    ≈≈idl : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      ı ○ σ ≈≈ σ
    ≈≈idr : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      σ ○ ı ≈≈ σ
    ≈≈wk : ∀ {α Γ Δ} {σ : Sub Γ Δ} {t : Tm Γ α} →
      ↑ ○ (t ∷ σ) ≈≈ σ
    ≈≈cons : ∀ {α Γ Δ Γ′} {σ : Sub Δ Γ} {t : Tm Δ α} {σ′ : Sub Γ′ Δ} →
      (t ∷ σ) ○ σ′ ≈≈ t [ σ′ ] ∷ (σ ○ σ′)
    ≈≈id∷ : ∀ {α Γ} →
      ı {α ∷ Γ} ≈≈ ø ∷ (ı ○ ↑)

-- ≈-Reasoning

≈setoid : {Γ : Ctx} {α : Ty} → Setoid _ _

≈setoid {Γ} {α} = record
  { Carrier = Tm Γ α
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans } }

module ≈-Reasoning {Γ} {α : Ty} = EqReasoning (≈setoid {Γ} {α})

-- ≈≈-Reasoning

≈≈setoid : {Γ Δ : Ctx} → Setoid _ _

≈≈setoid {Γ} {Δ} = record
  { Carrier = Sub Γ Δ
  ; _≈_ = _≈≈_
  ; isEquivalence = record
    { refl = ≈≈refl
    ; sym = ≈≈sym
    ; trans = ≈≈trans } }

module ≈≈-Reasoning {Γ} {Δ} = EqReasoning (≈≈setoid {Γ} {Δ})
