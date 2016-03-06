module NaturalNumbers.Syntax where

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   :  Ty
  _⇒_ : (α β : Ty) → Ty
  N   : Ty

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
    zero : ∀ {Γ} → Tm Γ N
    suc  : ∀ {Γ} (t : Tm Γ N) → Tm Γ N
    prim : ∀ {α Γ} (a : Tm Γ α) (b : Tm Γ (N ⇒ α ⇒ α)) (k : Tm Γ N) → Tm Γ α

  -- Substitutions: `Sub Γ Δ` transforms `Tm Δ α` into `Tm Γ α`.

  data Sub : (Γ Δ : Ctx) → Set where
    ı   : ∀ {Γ} → Sub Γ Γ
    _○_ : ∀ {Γ Δ Γ′} (σ : Sub Δ Γ) (τ : Sub Γ′ Δ) → Sub Γ′ Γ
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
    zero : ∀ {Γ} → Val Γ N
    suc  : ∀ {Γ} (u : Val Γ N) → Val Γ N

  data Env (Γ : Ctx) : Ctx → Set where
    []  : Env Γ []
    _∷_ : ∀ {α Δ} (u : Val Γ α) (ρ : Env Γ Δ) → Env Γ (α ∷ Δ)

  data NeVal (Γ : Ctx) : Ty → Set where
    var : ∀ {α} (x : Var Γ α) → NeVal Γ α
    app : ∀ {α β} (us : NeVal Γ (α ⇒ β)) (u : Val Γ α) → NeVal Γ β
    prim : ∀ {α} (u : Val Γ α) (v : Val Γ (N ⇒ α ⇒ α)) (us : NeVal Γ N) →
             NeVal Γ α


--
-- η-long β-normal forms.
--

mutual

  data Nf (Γ : Ctx) : Ty → Set where
    ne⋆ : ∀ (ns : NeNf Γ ⋆) → Nf Γ ⋆
    lam : ∀ {α β} (n : Nf (α ∷ Γ) β) → Nf Γ (α ⇒ β)
    neN  : ∀ (ns : NeNf Γ N) → Nf Γ N
    zero : Nf Γ N
    suc  : ∀ (n : Nf Γ N) → Nf Γ N

  data NeNf (Γ : Ctx) : Ty → Set where
    var : ∀ {α} (x : Var Γ α) → NeNf Γ α
    app : ∀ {α β} (ns : NeNf Γ (α ⇒ β)) (n : Nf Γ α) → NeNf Γ β
    prim : ∀ {α} (na : Nf Γ α) (nb : Nf Γ (N ⇒ α ⇒ α)) (ns : NeNf Γ N) →
             NeNf Γ α

--
-- Embedding of values and normal forms into terms.
--

embVar : ∀ {α Γ} (x : Var Γ α) → Tm Γ α
embVar zero = ø
embVar (suc x) = embVar x [ ↑ ]

sub-from-[] : ∀ {Γ} → Sub Γ []
sub-from-[] {[]} = ı
sub-from-[] {α ∷ Γ} = sub-from-[] ○ ↑

mutual

  embVal : ∀ {α Γ} (u : Val Γ α) → Tm Γ α
  embVal (ne us) = embNeVal us
  embVal (lam t ρ) = (ƛ t) [ embEnv ρ ]
  embVal zero = zero
  embVal (suc u) = suc (embVal u)

  embNeVal : ∀ {α Γ} (us : NeVal Γ α) → Tm Γ α
  embNeVal (var x) = embVar x
  embNeVal (app us u) = embNeVal us ∙ embVal u
  embNeVal (prim u v us) = prim (embVal u) (embVal v) (embNeVal us)

  embEnv : ∀ {Γ Δ} (ρ : Env Γ Δ) → Sub Γ Δ
  embEnv [] = sub-from-[]
  embEnv (u ∷ ρ) = embVal u ∷ embEnv ρ

mutual

  embNf : ∀ {α Γ} (n : Nf Γ α) → Tm Γ α
  embNf (ne⋆ ns) = embNeNf ns
  embNf (lam n) = ƛ embNf n
  embNf (neN ns) = embNeNf ns
  embNf zero = zero
  embNf (suc n) = suc (embNf n)

  embNeNf : ∀ {α Γ} (ns : NeNf Γ α) → Tm Γ α
  embNeNf (var x) = embVar x
  embNeNf (app ns n) = embNeNf ns ∙ embNf n
  embNeNf (prim na nb ns) = prim (embNf na) (embNf nb) (embNeNf ns)
