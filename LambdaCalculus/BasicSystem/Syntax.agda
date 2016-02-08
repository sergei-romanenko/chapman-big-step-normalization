module BasicSystem.Syntax where

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   :  Ty
  _⇒_ : (α β : Ty) → Ty

infixl 6 _[_]
infixr 6 _○_
infixr 5 _∷_
infixl 5 _∙_
infixr 3 ƛ_

-- Contexts.

data Ctx : Set where
  []  : Ctx
  _∷_ : (α : Ty) (Γ : Ctx)  → Ctx

mutual

  -- Terms.

  data Tm : (Γ : Ctx) (α : Ty) → Set where
    ø   : ∀ {α Γ} → Tm (α ∷ Γ) α
    _∙_ : ∀ {α β Γ} (t : Tm Γ (α ⇒ β)) (t′ : Tm Γ α) → Tm Γ β
    ƛ_  : ∀ {α β Γ} (t : Tm (α ∷ Γ) β) → Tm Γ (α ⇒ β)
    _[_] : ∀ {α Γ Δ} (t : Tm Δ α) (σ : Sub Γ Δ) → Tm Γ α

  -- Substitutions: `Sub Γ Δ` transforms `Tm Δ α` into `Tm Γ α`.

  data Sub : (Γ Δ : Ctx) → Set where
    ı   : ∀ {Γ} → Sub Γ Γ
    _○_ : ∀ {Γ Δ Γ′} (σ : Sub Δ Γ) (σ′ : Sub Γ′ Δ) → Sub Γ′ Γ
    _∷_ : ∀ {α Γ Δ} (t : Tm Γ α) (σ : Sub Γ Δ) → Sub Γ (α ∷ Δ)
    ↑  : ∀ {α Γ} → Sub (α ∷ Γ) Γ

--
-- Weak head normal forms.
--

data Var : (Γ : Ctx) (α : Ty) → Set where
  zero : ∀ {α Γ} → Var (α ∷ Γ) α
  suc  : ∀ {α β Γ} (x : Var Γ α) → Var (β ∷ Γ) α

mutual

  data Val : (Γ : Ctx) (α : Ty) → Set where
    ne  : ∀ {α Γ} (us : NeVal Γ α) → Val Γ α
    lam : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) → Val Γ (α ⇒ β)

  data Env (Γ : Ctx) : Ctx → Set where
    []  : Env Γ []
    _∷_ : ∀ {α Δ} (u : Val Γ α) (ρ : Env Γ Δ) → Env Γ (α ∷ Δ)

  data NeVal (Γ : Ctx) : Ty → Set where
    var : ∀ {α} (x : Var Γ α) → NeVal Γ α
    app : ∀ {α β} (us : NeVal Γ (α ⇒ β)) (u : Val Γ α) → NeVal Γ β


--
-- η-long β-normal forms.
--

mutual

  data Nf (Γ : Ctx) : Ty → Set where
    ne  : ∀ (ns : NeNf Γ ⋆) → Nf Γ ⋆
    lam : ∀ {α β} (n : Nf (α ∷ Γ) β) → Nf Γ (α ⇒ β)

  data NeNf (Γ : Ctx) : Ty → Set where
    var : ∀ {α} (x : Var Γ α) → NeNf Γ α
    app : ∀ {α β} (ns : NeNf Γ (α ⇒ β)) (n : Nf Γ α) → NeNf Γ β
