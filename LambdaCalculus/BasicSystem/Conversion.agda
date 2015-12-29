module BasicSystem.Conversion where
open import BasicSystem.Syntax

infix 10 _≃_
infix 10 _≃ˢ_

mutual
  data _≃_ : ∀ {Γ σ} → Tm Γ σ → Tm Γ σ → Set where
    -- equivalence closure
    refl  : ∀ {Γ σ}{t : Tm Γ σ} → t ≃ t
    sym   : ∀ {Γ σ}{t t' : Tm Γ σ} → t ≃ t' → t' ≃ t
    trans : ∀ {Γ σ}{t t' t'' : Tm Γ σ} → t ≃ t' → t' ≃ t'' → t ≃ t''

    -- congruence closure
    cong[]   : ∀ {Γ Δ σ}{t t' : Tm Δ σ}{ts ts' : Sub Γ Δ} → t ≃ t' →
               ts ≃ˢ ts' → t [ ts ] ≃ t' [ ts' ]

    congλ    : ∀ {Γ σ τ}{t t' : Tm (Γ < σ) τ} → t ≃ t' → λt t ≃ λt t'
    cong$    : ∀ {Γ σ τ}{t t' : Tm Γ (σ ⇒ τ)}{u u' : Tm Γ σ} → t ≃ t' →
                u ≃ u' → t $ u ≃ t' $ u'

    -- computation rules
    top< : ∀ {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} → top [ ts < t ] ≃ t 
    [][] : ∀ {B Γ Δ σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{us : Sub B Γ} →
           t [ ts ] [ us ] ≃ t [ ts ○ us ]
    []id : ∀ {Γ σ}{t : Tm Γ σ} → t [ id ] ≃ t

    λ[]  : ∀ {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{ts : Sub Γ Δ} → 
           λt t [ ts ] ≃ λt (t [ (ts ○ pop σ) < top ])
    $[]  : ∀ {Γ Δ σ τ}{t : Tm Δ (σ ⇒ τ)}{u : Tm Δ σ}{ts : Sub Γ Δ} →
           (t $ u) [ ts ] ≃ t [ ts ] $ (u [ ts ])
    β    : ∀ {Γ σ τ}{t : Tm (Γ < σ) τ}{u : Tm Γ σ} →
           λt t $ u ≃ t [ id < u ]
    η    : ∀ {Γ σ τ}{t : Tm Γ (σ ⇒ τ)} → t ≃  λt (t [ pop σ ] $ top)

  data _≃ˢ_ : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set where
    -- equivalence closure
    reflˢ  : ∀ {Γ Δ}{ts : Sub Γ Δ} → ts ≃ˢ ts
    symˢ   : ∀ {Γ Δ}{ts ts' : Sub Γ Δ} → ts ≃ˢ ts' → ts' ≃ˢ ts
    transˢ : ∀ {Γ Δ}{ts ts' ts'' : Sub Γ Δ} → ts ≃ˢ ts' → 
             ts' ≃ˢ ts'' → ts ≃ˢ ts''
  
    -- congruence closure
    cong<  : ∀ {Γ Δ σ}{ts ts' : Sub Γ Δ}{t t' : Tm Γ σ} → ts ≃ˢ ts' →
             t ≃ t' → ts < t ≃ˢ ts' < t'
    cong○  : ∀ {B Γ Δ}{ts ts' : Sub Γ Δ}{us us' : Sub B Γ} → ts ≃ˢ ts' →
             us ≃ˢ us' → ts ○ us ≃ˢ ts' ○ us'

    -- computation rules
    idcomp  : ∀ {Γ σ} → id ≃ˢ (id {Γ} ○ pop σ) < top
    popcomp : ∀ {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} → 
              pop σ ○ (ts < t) ≃ˢ ts
    leftidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → id ○ ts ≃ˢ ts
    rightidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → ts ○ id ≃ˢ ts
    assoc   : ∀ {A B Γ Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} →
              (ts ○ us) ○ vs ≃ˢ ts ○ (us ○ vs)
    comp<   : ∀ {B Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ}{us : Sub B Γ} →
              (ts < t) ○ us ≃ˢ (ts ○ us) < t [ us ]
