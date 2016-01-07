module BasicSystem.Conversion where

open import BasicSystem.Syntax

infix 4 _≈_
infix 4 _≃_

mutual
  data _≈_ : ∀ {Γ σ} → Tm Γ σ → Tm Γ σ → Set where
    -- equivalence closure
    ≈refl  : ∀ {Γ σ}{t : Tm Γ σ} → t ≈ t
    ≈sym   : ∀ {Γ σ}{t t' : Tm Γ σ} → t ≈ t' → t' ≈ t
    ≈trans : ∀ {Γ σ}{t t' t'' : Tm Γ σ} → t ≈ t' → t' ≈ t'' → t ≈ t''

    -- congruence closure
    cong[]   : ∀ {Γ Δ σ}{t t' : Tm Δ σ}{ts ts' : Sub Γ Δ} → t ≈ t' →
               ts ≃ ts' → t [ ts ] ≈ t' [ ts' ]

    congλ    : ∀ {Γ σ τ}{t t' : Tm (Γ < σ) τ} → t ≈ t' → ƛ t ≈ ƛ t'
    cong∙    : ∀ {Γ σ τ}{t t' : Tm Γ (σ ⇒ τ)}{u u' : Tm Γ σ} → t ≈ t' →
                u ≈ u' → t ∙ u ≈ t' ∙ u'

    -- computation rules
    ø<   : ∀ {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} → ø [ ts < t ] ≈ t 
    [][] : ∀ {B Γ Δ σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{us : Sub B Γ} →
           t [ ts ] [ us ] ≈ t [ ts ○ us ]
    []id : ∀ {Γ σ}{t : Tm Γ σ} → t [ ı ] ≈ t

    λ[]  : ∀ {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{ts : Sub Γ Δ} → 
           ƛ t [ ts ] ≈ ƛ (t [ (ts ○ ↑ σ) < ø ])
    ∙[]  : ∀ {Γ Δ σ τ}{t : Tm Δ (σ ⇒ τ)}{u : Tm Δ σ}{ts : Sub Γ Δ} →
           (t ∙ u) [ ts ] ≈ t [ ts ] ∙ (u [ ts ])
    β    : ∀ {Γ σ τ}{t : Tm (Γ < σ) τ}{u : Tm Γ σ} →
           ƛ t ∙ u ≈ t [ ı < u ]
    η    : ∀ {Γ σ τ}{t : Tm Γ (σ ⇒ τ)} → t ≈  ƛ (t [ ↑ σ ] ∙ ø)

  data _≃_ : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set where
    -- equivalence closure
    ≃refl  : ∀ {Γ Δ}{ts : Sub Γ Δ} → ts ≃ ts
    ≃sym   : ∀ {Γ Δ}{ts ts' : Sub Γ Δ} → ts ≃ ts' → ts' ≃ ts
    ≃trans : ∀ {Γ Δ}{ts ts' ts'' : Sub Γ Δ} → ts ≃ ts' → 
             ts' ≃ ts'' → ts ≃ ts''
  
    -- congruence closure
    cong<  : ∀ {Γ Δ σ}{ts ts' : Sub Γ Δ}{t t' : Tm Γ σ} → ts ≃ ts' →
             t ≈ t' → ts < t ≃ ts' < t'
    cong○  : ∀ {B Γ Δ}{ts ts' : Sub Γ Δ}{us us' : Sub B Γ} → ts ≃ ts' →
             us ≃ us' → ts ○ us ≃ ts' ○ us'

    -- computation rules
    idcomp  : ∀ {Γ σ} → ı ≃ (ı {Γ} ○ ↑ σ) < ø
    ↑comp : ∀ {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} → 
              ↑ σ ○ (ts < t) ≃ ts
    leftidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → ı ○ ts ≃ ts
    rightidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → ts ○ ı ≃ ts
    assoc   : ∀ {A B Γ Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} →
              (ts ○ us) ○ vs ≃ ts ○ (us ○ vs)
    comp<   : ∀ {B Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ}{us : Sub B Γ} →
              (ts < t) ○ us ≃ (ts ○ us) < t [ us ]
