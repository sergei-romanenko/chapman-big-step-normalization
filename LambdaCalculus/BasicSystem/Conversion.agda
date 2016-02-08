module BasicSystem.Conversion where

open import BasicSystem.Syntax

infix 4 _≈_
infix 4 _≃_

mutual
  data _≈_ : ∀ {Γ α} → Tm Γ α → Tm Γ α → Set where
    -- equivalence closure
    ≈refl  : ∀ {Γ α}{t : Tm Γ α} → t ≈ t
    ≈sym   : ∀ {Γ α}{t t' : Tm Γ α} → t ≈ t' → t' ≈ t
    ≈trans : ∀ {Γ α}{t t' t'' : Tm Γ α} → t ≈ t' → t' ≈ t'' → t ≈ t''

    -- congruence closure
    cong[]   : ∀ {Γ Δ α}{t t' : Tm Δ α}{ts ts' : Sub Γ Δ} → t ≈ t' →
               ts ≃ ts' → t [ ts ] ≈ t' [ ts' ]

    congλ    : ∀ {Γ α β}{t t' : Tm (α ∷ Γ) β} → t ≈ t' → (ƛ t) ≈ (ƛ t')
    cong∙    : ∀ {Γ α β}{t t' : Tm Γ (α ⇒ β)}{u u' : Tm Γ α} → t ≈ t' →
                u ≈ u' → t ∙ u ≈ t' ∙ u'

    -- computation rules
    ø<   : ∀ {Γ Δ α}{ts : Sub Γ Δ}{t : Tm Γ α} → ø [ t ∷ ts ] ≈ t 
    [][] : ∀ {B Γ Δ α}{t : Tm Δ α}{ts : Sub Γ Δ}{us : Sub B Γ} →
           t [ ts ] [ us ] ≈ t [ ts ○ us ]
    []id : ∀ {Γ α}{t : Tm Γ α} → t [ ı ] ≈ t

    λ[]  : ∀ {Γ Δ α β}{t : Tm (α ∷ Δ) β}{ts : Sub Γ Δ} → 
           (ƛ t) [ ts ] ≈ (ƛ t [ ø ∷ (ts ○ ↑) ])
    ∙[]  : ∀ {Γ Δ α β}{t : Tm Δ (α ⇒ β)}{u : Tm Δ α}{ts : Sub Γ Δ} →
           (t ∙ u) [ ts ] ≈ t [ ts ] ∙ (u [ ts ])
    ≈βσ  : ∀ {Γ α β}{t : Tm (α ∷ Γ) β}{u : Tm Γ α} →
           (ƛ t) ∙ u ≈ t [ u ∷ ı ]
    ≈η    : ∀ {Γ α β}{t : Tm Γ (α ⇒ β)} → t ≈  (ƛ t [ ↑ ] ∙ ø)

  data _≃_ : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set where
    -- equivalence closure
    ≃refl  : ∀ {Γ Δ}{ts : Sub Γ Δ} → ts ≃ ts
    ≃sym   : ∀ {Γ Δ}{ts ts' : Sub Γ Δ} → ts ≃ ts' → ts' ≃ ts
    ≃trans : ∀ {Γ Δ}{ts ts' ts'' : Sub Γ Δ} → ts ≃ ts' → 
             ts' ≃ ts'' → ts ≃ ts''
  
    -- congruence closure
    cong<  : ∀ {Γ Δ α}{ts ts' : Sub Γ Δ}{t t' : Tm Γ α} → ts ≃ ts' →
             t ≈ t' → t ∷ ts ≃ t' ∷ ts'
    cong○  : ∀ {B Γ Δ}{ts ts' : Sub Γ Δ}{us us' : Sub B Γ} → ts ≃ ts' →
             us ≃ us' → ts ○ us ≃ ts' ○ us'

    -- computation rules
    idcomp  : ∀ {Γ α} → ı {α ∷ Γ} ≃  ø ∷ (ı ○ ↑)
    ↑comp : ∀ {Γ Δ α}{ts : Sub Γ Δ}{t : Tm Γ α} → 
              ↑ ○ (t ∷ ts) ≃ ts
    leftidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → ı ○ ts ≃ ts
    rightidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → ts ○ ı ≃ ts
    assoc   : ∀ {A B Γ Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} →
              (ts ○ us) ○ vs ≃ ts ○ (us ○ vs)
    comp<   : ∀ {B Γ Δ α}{ts : Sub Γ Δ}{t : Tm Γ α}{us : Sub B Γ} →
              (t ∷ ts) ○ us ≃ t [ us ] ∷ (ts ○ us)
