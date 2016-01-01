module FiniteProducts.Conversion where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax

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

    congλ    : ∀ {Γ σ τ}{t t' : Tm (Γ < σ) τ} → t ≈ t' → λt t ≈ λt t'
    cong$    : ∀ {Γ σ τ}{t t' : Tm Γ (σ ⇒ τ)}{u u' : Tm Γ σ} → t ≈ t' →
                u ≈ u' → t $ u ≈ t' $ u'

    cong<,> : ∀ {Γ σ τ}{t t' : Tm Γ σ}{u u' : Tm Γ τ} → 
              t ≈ t' → u ≈ u' → < t , u > ≈ < t' , u' >
    congfst : ∀ {Γ σ τ}{t t' : Tm Γ (σ * τ)} →
              t ≈ t' → fst t ≈ fst t'
    congsnd : ∀ {Γ σ τ}{t t' : Tm Γ (σ * τ)} →
              t ≈ t' → snd t ≈ snd t'

    -- computation rules
    top< : ∀ {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} → top [ ts < t ] ≈ t 
    [][] : ∀ {B Γ Δ σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{us : Sub B Γ} →
           t [ ts ] [ us ] ≈ t [ ts ○ us ]
    []id : ∀ {Γ σ}{t : Tm Γ σ} → t [ id ] ≈ t

    λ[]  : ∀ {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{ts : Sub Γ Δ} → 
           λt t [ ts ] ≈ λt (t [ (ts ○ pop σ) < top ])
    $[]  : ∀ {Γ Δ σ τ}{t : Tm Δ (σ ⇒ τ)}{u : Tm Δ σ}{ts : Sub Γ Δ} →
           (t $ u) [ ts ] ≈ t [ ts ] $ (u [ ts ])
    βλ    : ∀ {Γ σ τ}{t : Tm (Γ < σ) τ}{u : Tm Γ σ} →
            λt t $ u ≈ t [ id < u ]
    ηλ    : ∀ {Γ σ τ}{t : Tm Γ (σ ⇒ τ)} → t ≈  λt (t [ pop σ ] $ top)

    void[] : ∀ {Γ Δ}{ts : Sub Γ Δ} → void [ ts ] ≈ void 
    <,>[] : ∀ {Γ Δ σ τ}{t : Tm Δ σ}{u : Tm Δ τ}{ts : Sub Γ Δ} →
            < t , u > [ ts ] ≈ < t [ ts ] , u [ ts ] >
    fst[] : ∀ {Γ Δ σ τ}{t : Tm Δ (σ * τ)}{ts : Sub Γ Δ} →
            fst t [ ts ] ≈ fst (t [ ts ])
    snd[] : ∀ {Γ Δ σ τ}{t : Tm Δ (σ * τ)}{ts : Sub Γ Δ} →
            snd t [ ts ] ≈ snd (t [ ts ])
    βfst : ∀ {Γ σ τ}{t : Tm Γ σ}{u : Tm Γ τ} → fst < t , u > ≈ t
    βsnd : ∀ {Γ σ τ}{t : Tm Γ σ}{u : Tm Γ τ} → snd < t , u > ≈ u
    η<,> : ∀ {Γ σ τ}{t : Tm Γ (σ * τ)} → t ≈ < fst t , snd t >
    ηvoid : ∀ {Γ}{t : Tm Γ One} → t ≈ void

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
    idcomp  : ∀ {Γ σ} → id ≃ (id {Γ} ○ pop σ) < top
    popcomp : ∀ {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} → 
              pop σ ○ (ts < t) ≃ ts
    leftidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → id ○ ts ≃ ts
    rightidˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → ts ○ id ≃ ts
    assoc   : ∀ {A B Γ Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} →
              (ts ○ us) ○ vs ≃ ts ○ (us ○ vs)
    comp<   : ∀ {B Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ}{us : Sub B Γ} →
              (ts < t) ○ us ≃ (ts ○ us) < t [ us ]
