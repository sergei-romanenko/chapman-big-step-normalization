module FiniteProducts.OPE where

open import FiniteProducts.Syntax


--
-- Weakening contexts by means of order preserving embeddings.
--

infix 4 _≤_

data _≤_ : Ctx → Ctx → Set where
  ≤[] : [] ≤ []
  ≤lift : ∀ {α Γ Δ} → Γ ≤ Δ → α ∷ Γ ≤ α ∷ Δ
  ≤weak : ∀ {α Γ Δ} → Γ ≤ Δ → α ∷ Γ ≤ Δ

≤id : ∀ {Γ} → Γ ≤ Γ
≤id {[]}     = ≤[]
≤id {α ∷ Γ} = ≤lift ≤id

wk : ∀ {α Γ} → α ∷ Γ ≤ Γ
wk {α} = ≤weak ≤id

--
-- Applying OPEs.
--

var≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (x : Var Δ α) → Var Γ α
var≤ ≤[] x = x
var≤ (≤weak η) x = suc (var≤ η x)
var≤ (≤lift η) zero = zero
var≤ (≤lift η) (suc x) = suc (var≤ η x)

mutual

  val≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (u : Val Δ α) → Val Γ α
  val≤ η (ne us) = ne (neVal≤ η us)
  val≤ η (lam t ρ) = lam t (env≤ η ρ)
  val≤ η void = void
  val≤ η (pair u v) = pair (val≤ η u) (val≤ η v)

  neVal≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (us : NeVal Δ α) → NeVal Γ α
  neVal≤ η (var x) = var (var≤ η x)
  neVal≤ η (app us u) = app (neVal≤ η us) (val≤ η u)
  neVal≤ η (fst us) = fst (neVal≤ η us)
  neVal≤ η (snd us) = snd (neVal≤ η us)

  env≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (ρ : Env Δ α) → Env Γ α
  env≤ η [] = []
  env≤ η (u ∷ ρ) = val≤ η u ∷ env≤ η ρ

mutual

  nf≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (n : Nf Δ α) → Nf Γ α
  nf≤ η (ne ns) = ne (neNf≤ η ns)
  nf≤ η (lam n) = lam (nf≤ (≤lift η) n)
  nf≤ η void = void
  nf≤ η (pair na nb) = pair (nf≤ η na) (nf≤ η nb)

  neNf≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) {α} (ns : NeNf Δ α) → NeNf Γ α
  neNf≤ η (var x) = var (var≤ η x)
  neNf≤ η (app ns n) = app (neNf≤ η ns) (nf≤ η n)
  neNf≤ η (fst ns) = fst (neNf≤ η ns)
  neNf≤ η (snd ns) = snd (neNf≤ η ns)

--
-- ≤ to Sub.
--

≤2sub : ∀ {Γ Δ} (η : Γ ≤ Δ) → Sub Γ Δ
≤2sub ≤[] = ı
≤2sub (≤weak η) = ≤2sub η ○ ↑
≤2sub (≤lift η) = ø ∷ ≤2sub η ○ ↑

--
-- Identity environments.
--

id-env : ∀ {Γ} → Env Γ Γ
id-env {[]} = []
id-env {α ∷ Γ} = ne (var zero) ∷ env≤ wk id-env

--
-- Composing OPEs.
--

infixr 6 _●_

_●_ : ∀ {Β Γ Δ} (η : Β ≤ Γ) (η′ : Γ ≤ Δ) → Β ≤ Δ
≤[] ● ≤[] = ≤[]
≤weak η ● η′ = ≤weak (η ● η′)
≤lift η ● ≤weak η′ = ≤weak (η ● η′)
≤lift η ● ≤lift η′ = ≤lift (η ● η′)
