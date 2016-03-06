module FullSystem.Conversion where

import Relation.Binary.EqReasoning as EqReasoning

open import FullSystem.Utils
open import FullSystem.Syntax

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
    ≈[○] : ∀ {α Γ Δ Γ′} {t : Tm Δ α} {σ : Sub Γ Δ} {τ : Sub Γ′ Γ} →
      t [ σ ○ τ ] ≈ t [ σ ] [ τ ]
    ≈ƛ[] : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} →
      (ƛ t) [ σ ] ≈ (ƛ t [ ø ∷ (σ ○ ↑) ])
    ≈∙[] : ∀ {α β Γ Δ} {f : Tm Δ (α ⇒ β)} {a : Tm Δ α} {σ : Sub Γ Δ} →
      (f ∙ a) [ σ ] ≈ f [ σ ] ∙ a [ σ ]
    ≈βσ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {σ : Sub Γ Δ} {a : Tm Γ α} →
      (ƛ t) [ σ ] ∙ a ≈ t [ a ∷ σ ]
    ≈η : ∀ {α β Γ} {t : Tm Γ (α ⇒ β)} →
      t ≈ (ƛ (t [ ↑ ] ∙ ø))
    ≈cong-pair : ∀ {α β Γ} {f₁ f₂ : Tm Γ α} {s₁ s₂ : Tm Γ β} → 
      f₁ ≈ f₂ → s₁ ≈ s₂ → pair f₁ s₁ ≈ pair f₂ s₂
    ≈cong-fst  : ∀ {α β Γ} {t₁ t₂ : Tm Γ (α * β)} →
      t₁ ≈ t₂ → fst t₁ ≈ fst t₂
    ≈cong-snd  : ∀ {α β Γ} {t₁ t₂ : Tm Γ (α * β)} →
      t₁ ≈ t₂ → snd t₁ ≈ snd t₂
    ≈void[] : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      void [ σ ] ≈ void 
    ≈pair[] : ∀ {α β Γ Δ} {f : Tm Δ α} {s : Tm Δ β} {σ : Sub Γ Δ} →
      pair f s [ σ ] ≈ pair (f [ σ ]) (s [ σ ])
    ≈fst[] : ∀ {α β Γ Δ} {t : Tm Δ (α * β)} {σ : Sub Γ Δ} →
      fst t [ σ ] ≈ fst (t [ σ ])
    ≈snd[] : ∀ {α β Γ Δ} {t : Tm Δ (α * β)} {σ : Sub Γ Δ} →
      snd t [ σ ] ≈ snd (t [ σ ])
    ≈βfst : ∀ {α β Γ} {f : Tm Γ α} {s : Tm Γ β} →
      fst (pair f s) ≈ f
    ≈βsnd : ∀ {α β Γ} {f : Tm Γ α} {s : Tm Γ β} →
      snd (pair f s) ≈ s
    ≈ηpair : ∀ {Γ α β} {t : Tm Γ (α * β)} →
      t ≈ pair (fst t) (snd t)
    ≈ηvoid : ∀ {Γ} {t : Tm Γ One} →
      t ≈ void
    ≈cong-suc  : ∀ {Γ} {t₁ t₂ : Tm Γ N} (t₁≈t₂ : t₁ ≈ t₂) →
      suc t₁ ≈ suc t₂
    ≈cong-prim : ∀ {α Γ} {a₁ a₂ : Tm Γ α} {b₁ b₂} {k₁ k₂} → 
      (a₁≈a₂ : a₁ ≈ a₂) (b₁≈b₂ : b₁ ≈ b₂) (k₁≈k₂ : k₁ ≈ k₂) →
      prim a₁ b₁ k₁ ≈ prim a₂ b₂ k₂
    ≈zero[] : ∀ {Γ Δ} {σ : Sub Γ Δ} →
      zero [ σ ] ≈ zero
    ≈suc[]  : ∀ {Γ Δ} {t : Tm Δ N} {σ : Sub Γ Δ} →
      suc t [ σ ] ≈ suc (t [ σ ])
    ≈prim[] : ∀ {α Γ Δ} {a : Tm Δ α} {b k} {σ : Sub Γ Δ} → 
      prim a b k [ σ ] ≈ prim (a [ σ ]) (b [ σ ]) (k [ σ ])
    ≈primz : ∀ {α Γ} {a : Tm Γ α} {b} →
      prim a b zero ≈ a
    ≈prims : ∀ {α Γ} {a : Tm Γ α} {b k} → 
      prim a b (suc k) ≈ ((b ∙ k) ∙ prim a b k)

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
    ≈≈cons : ∀ {α Γ Δ Γ′} {σ : Sub Δ Γ} {t : Tm Δ α} {τ : Sub Γ′ Δ} →
      (t ∷ σ) ○ τ ≈≈ t [ τ ] ∷ (σ ○ τ)
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
