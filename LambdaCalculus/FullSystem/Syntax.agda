module FullSystem.Syntax where

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty
  N   : Ty
  One : Ty
  _*_ : Ty → Ty → Ty


infixr 10 _⇒_

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

mutual
  data Tm : Con → Ty → Set where
    top  : ∀ {Γ σ} → Tm (Γ < σ) σ
    _[_] : ∀ {Γ Δ σ} → Tm Δ σ → Sub Γ Δ → Tm Γ σ
    λt    : ∀ {Γ σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
    _$_  : ∀ {Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
    zero : ∀ {Γ} → Tm Γ N
    suc  : ∀ {Γ} → Tm Γ N → Tm Γ N
    prim : ∀ {Γ σ} → Tm Γ σ → Tm Γ (N ⇒ σ ⇒ σ) → Tm Γ N → Tm Γ σ
    void  : ∀ {Γ} → Tm Γ One
    <_,_> : ∀ {Γ σ τ} → Tm Γ σ → Tm Γ τ → Tm Γ (σ * τ)
    fst   : ∀ {Γ σ τ} → Tm Γ (σ * τ) → Tm Γ σ
    snd   : ∀ {Γ σ τ} → Tm Γ (σ * τ) → Tm Γ τ

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
    λv  : ∀ {Γ Δ σ τ} → Tm (Δ < σ) τ → Env Γ Δ → 
          Val Γ (σ ⇒ τ)
    nev : ∀ {Γ σ} → NeV Γ σ → Val Γ σ
    zerov : ∀ {Γ} → Val Γ N
    sucv  : ∀ {Γ} → Val Γ N → Val Γ N
    voidv  : ∀ {Γ} → Val Γ One
    <_,_>v : ∀ {Γ σ τ} → Val Γ σ → Val Γ τ → Val Γ (σ * τ)

  data Env : Con → Con → Set where
    ε   : ∀ {Γ} → Env Γ ε
    _<<_ : ∀ {Γ Δ σ} → Env Γ Δ → Val Γ σ → Env Γ (Δ < σ)

  data NeV : Con → Ty → Set where
    varV  : ∀ {Γ σ} → Var Γ σ → NeV Γ σ
    appV  : ∀ {Γ σ τ} → NeV Γ (σ ⇒ τ) → Val Γ σ → NeV Γ τ
    primV : ∀ {Γ σ} → Val Γ σ → Val Γ (N ⇒ σ ⇒ σ) → NeV Γ N → NeV Γ σ
    fstV : ∀ {Γ σ τ} → NeV Γ (σ * τ) → NeV Γ σ
    sndV : ∀ {Γ σ τ} → NeV Γ (σ * τ) → NeV Γ τ

mutual
  data Nf : Con → Ty → Set where
    λn    : ∀ {Γ σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    neι   : ∀ {Γ} → NeN Γ ι → Nf Γ ι
    neN   : ∀ {Γ} → NeN Γ N → Nf Γ N
    zeron : ∀ {Γ} → Nf Γ N
    sucn  : ∀ {Γ} → Nf Γ N → Nf Γ N
    voidn  : ∀ {Γ} → Nf Γ One
    <_,_>n : ∀ {Γ σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ * τ)

  data NeN : Con → Ty → Set where
    varN  : ∀ {Γ σ} → Var Γ σ → NeN Γ σ
    appN  : ∀ {Γ σ τ} → NeN Γ (σ ⇒ τ) → Nf Γ σ → NeN Γ τ
    primN : ∀ {Γ σ} → Nf Γ σ → Nf Γ (N ⇒ σ ⇒ σ) → NeN Γ N → NeN Γ σ
    fstN : ∀ {Γ σ τ} → NeN Γ (σ * τ) → NeN Γ σ
    sndN : ∀ {Γ σ τ} → NeN Γ (σ * τ) → NeN Γ τ
