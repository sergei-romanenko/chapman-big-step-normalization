module FiniteProducts.Syntax where

data Ty : Set where
  ι   : Ty  
  _⇒_ : Ty → Ty → Ty
  One : Ty
  _×_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

mutual
  data Tm : Con → Ty → Set where
    top   : ∀ {Γ σ} → Tm (Γ < σ) σ
    _[_]  : ∀ {Γ Δ σ} → Tm Δ σ → Sub Γ Δ → Tm Γ σ
    λt     : ∀ {Γ σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
    _$_   : ∀ {Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
    void  : ∀ {Γ} → Tm Γ One
    <_,_> : ∀ {Γ σ τ} → Tm Γ σ → Tm Γ τ → Tm Γ (σ × τ)
    fst   : ∀ {Γ σ τ} → Tm Γ (σ × τ) → Tm Γ σ
    snd   : ∀ {Γ σ τ} → Tm Γ (σ × τ) → Tm Γ τ

  data Sub : Con → Con → Set where
    pop  : ∀ {Γ} σ → Sub (Γ < σ) Γ
    _<_ : ∀ {Γ Δ σ} → Sub Γ Δ → Tm Γ σ → Sub Γ (Δ < σ)
    id   : ∀ {Γ} → Sub Γ Γ
    _○_  : ∀ {B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ

data Var : Con → Ty → Set where
  vZ : ∀ {Γ σ} → Var (Γ < σ) σ
  vS : ∀ {Γ σ} τ → Var Γ σ → Var (Γ < τ) σ

mutual
  data Val : Con → Ty → Set where
    λv     : ∀ {Γ Δ σ τ} → Tm (Δ < σ) τ → Env Γ Δ → Val Γ (σ ⇒ τ)
    voidv  : ∀ {Γ} → Val Γ One
    <_,_>v : ∀ {Γ σ τ} → Val Γ σ → Val Γ τ → Val Γ (σ × τ)
    nev    : ∀ {Γ σ} → NeV Γ σ → Val Γ σ
    
  data Env : Con → Con → Set where
    ε   : ∀ {Γ} → Env Γ ε
    _<<_ : ∀ {Γ Δ σ} → Env Γ Δ → Val Γ σ → Env Γ (Δ < σ)

  data NeV : Con → Ty → Set where
    varV : ∀ {Γ σ} → Var Γ σ → NeV Γ σ
    appV : ∀ {Γ σ τ} → NeV Γ (σ ⇒ τ) → Val Γ σ → NeV Γ τ
    fstV : ∀ {Γ σ τ} → NeV Γ (σ × τ) → NeV Γ σ
    sndV : ∀ {Γ σ τ} → NeV Γ (σ × τ) → NeV Γ τ

mutual
  data Nf : Con → Ty → Set where
    λn     : ∀ {Γ σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    voidn  : ∀ {Γ} → Nf Γ One
    <_,_>n : ∀ {Γ σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ × τ)
    ne     : ∀ {Γ} → NeN Γ ι → Nf Γ ι

  data NeN : Con → Ty → Set where
    varN : ∀ {Γ σ} → Var Γ σ → NeN Γ σ
    appN : ∀ {Γ σ τ} → NeN Γ (σ ⇒ τ) → Nf Γ σ → NeN Γ τ
    fstN : ∀ {Γ σ τ} → NeN Γ (σ × τ) → NeN Γ σ
    sndN : ∀ {Γ σ τ} → NeN Γ (σ × τ) → NeN Γ τ
