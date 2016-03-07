module NaturalNumbers.BigStep where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax

--
-- Big-step semantics (the graph of the recursive function).
--

infix 4 _⇓_ _⟨∙⟩_⇓_

data _⟨∙⟩_⇓_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α) (w : Nf β) → Set where
  K0⇓ : ∀ {α β u} →
    K0 {α} {β} ⟨∙⟩ u ⇓ K1 u
  K1⇓ : ∀ {α β u v} →
    K1 {α} {β} u ⟨∙⟩ v ⇓ u
  S0⇓ : ∀ {α β γ u} →
    S0 {α} {β} {γ} ⟨∙⟩ u ⇓ S1 u
  S1⇓ : ∀ {α β γ u v} →
    S1 {α} {β} {γ} u ⟨∙⟩ v ⇓ S2 u v
  S2⇓ : ∀ {α β γ u v w w′ w′′ w′′′}
    (p : u ⟨∙⟩ w ⇓ w′) (q : v ⟨∙⟩ w ⇓ w′′) (r : w′ ⟨∙⟩ w′′ ⇓ w′′′) →
    S2 {α} {β} {γ} u v ⟨∙⟩ w ⇓ w′′′
  Suc0⇓ : ∀ {u} →
    Suc0 ⟨∙⟩ u ⇓ Suc1 u
  R0⇓ : ∀ {α u} →
    R0 {α} ⟨∙⟩ u ⇓ R1 u
  R1⇓ : ∀ {α u v} →
    R1 {α} u ⟨∙⟩ v ⇓ R2 u v
  R2z⇓ : ∀ {α u v} → 
    R2 {α} u v ⟨∙⟩ Zero0 ⇓ u
  R2s⇓ : ∀ {α u v w w′ w′′ w′′′} →
    v ⟨∙⟩ w ⇓ w′ → 
    R2 u v ⟨∙⟩ w ⇓ w′′ → 
    w′ ⟨∙⟩ w′′ ⇓ w′′′ →
    R2 {α} u v ⟨∙⟩ Suc1 w ⇓ w′′′

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  Zero⇓ :
    Zero ⇓ Zero0
  Suc⇓ :
    Suc ⇓ Suc0
  R⇓ : ∀ {α} →
    R {α} ⇓ R0

--
-- Structurally recursive normalizer.
--

_⟨∙⟩_&_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α)
  {w} (uv⇓ : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w

K0 ⟨∙⟩ v & K0⇓ = K1 v , refl
K1 u ⟨∙⟩ v & K1⇓ = u , refl
S0 ⟨∙⟩ v & S0⇓ = S1 v , refl
S1 u ⟨∙⟩ v & S1⇓ = S2 u v , refl
S2 u v ⟨∙⟩ w & S2⇓ uw⇓ vw⇓ uwvw⇓
  with u ⟨∙⟩ w & uw⇓ | v ⟨∙⟩ w & vw⇓
... | u′ , refl | v′ , refl = u′ ⟨∙⟩ v′ & uwvw⇓
Suc0 ⟨∙⟩ u & Suc0⇓ = Suc1 u , refl
R0 ⟨∙⟩ u & R0⇓ = R1 u , refl
R1 u ⟨∙⟩ v & R1⇓ = R2 u v , refl
R2 u v ⟨∙⟩ Zero0 & R2z⇓ = u , refl
R2 u v ⟨∙⟩ Suc1 w & R2s⇓ ⇓w′ ⇓w′′ ⇓w′′′
  with v ⟨∙⟩ w & ⇓w′ | R2 u v  ⟨∙⟩ w & ⇓w′′
... | w′ , refl | w′′ , refl = w′ ⟨∙⟩ w′′ & ⇓w′′′

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u

eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (A⇓ x⇓ y⇓ ⇓w)
  with eval x x⇓ | eval y y⇓
... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w
eval Zero Zero⇓ = Zero0 , refl
eval Suc Suc⇓ = Suc0 , refl
eval R R⇓ = R0 , refl

--
-- Determinism: x ⇓ u → x ⇓ v → u ≡ v
--

⟨∙⟩⇓-det : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α} {w w′ : Nf β} →
  u ⟨∙⟩ v ⇓ w → u ⟨∙⟩ v ⇓ w′ → w ≡ w′

⟨∙⟩⇓-det K0⇓ K0⇓ = refl
⟨∙⟩⇓-det K1⇓ K1⇓ = refl
⟨∙⟩⇓-det S0⇓ S0⇓ = refl
⟨∙⟩⇓-det S1⇓ S1⇓ = refl
⟨∙⟩⇓-det (S2⇓ p q r) (S2⇓ p′ q′ r′)
  rewrite ⟨∙⟩⇓-det p p′ | ⟨∙⟩⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl
⟨∙⟩⇓-det Suc0⇓ Suc0⇓ = refl
⟨∙⟩⇓-det R0⇓ R0⇓ = refl
⟨∙⟩⇓-det R1⇓ R1⇓ = refl
⟨∙⟩⇓-det R2z⇓ R2z⇓ = refl
⟨∙⟩⇓-det (R2s⇓ p q r) (R2s⇓ p′ q′ r′)
  rewrite ⟨∙⟩⇓-det p p′ | ⟨∙⟩⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl

⇓-det : ∀ {α} {x : Tm α} {u u′ : Nf α} →
  x ⇓ u → x ⇓ u′ → u ≡ u′

⇓-det K⇓ K⇓ = refl
⇓-det S⇓ S⇓ = refl
⇓-det (A⇓ p q r) (A⇓ p′ q′ r′)
  rewrite ⇓-det p p′ | ⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl
⇓-det Zero⇓ Zero⇓ = refl
⇓-det Suc⇓ Suc⇓ = refl
⇓-det R⇓ R⇓ = refl
