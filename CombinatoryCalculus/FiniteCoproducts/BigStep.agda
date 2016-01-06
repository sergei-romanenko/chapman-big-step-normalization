module FiniteCoproducts.BigStep where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax

--
-- Big step semantics (the graph of the recursive function).
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
  C0⇓ : ∀ {α β γ u} →
    C0 {α} {β} {γ} ⟨∙⟩ u ⇓ C1 u
  C1⇓ : ∀ {α β γ u v} → 
    C1 {α} {β} {γ} u ⟨∙⟩ v ⇓ C2 u v
  C2l⇓ : ∀ {α β γ u v w w′} →
    u ⟨∙⟩ w ⇓ w′ →
    C2 {α} {β} {γ} u v ⟨∙⟩ Inl1 w ⇓ w′
  C2r⇓ : ∀ {α β γ u v w w′} →
    v ⟨∙⟩ w ⇓ w′ →
    C2 {α} {β} {γ} u v ⟨∙⟩ Inr1 w ⇓ w′ 
  Inl0⇓ : ∀ {α β u} →
    Inl0 {α} {β} ⟨∙⟩ u ⇓ Inl1 u
  Inr0⇓ : ∀ {α β u} →
    Inr0 {α} {β} ⟨∙⟩ u ⇓ Inr1 u

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  NE⇓ : ∀ {α} →
    NE {α} ⇓ NE0
  Inl⇓ : ∀ {α β} →
    Inl {α} {β} ⇓ Inl0
  Inr⇓ : ∀ {α β} →
    Inr {α} {β} ⇓ Inr0
  C⇓ : ∀ {α β γ} →
    C {α} {β} {γ} ⇓ C0

--
-- Structurally recursive normalizer.
--

_⟨∙⟩_&_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α)
  {w} (uv⇓ : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w

K0 ⟨∙⟩ v & K0⇓ = K1 v , refl
K1 u ⟨∙⟩ v & K1⇓ = u , refl
S0 ⟨∙⟩ v & S0⇓ = S1 v , refl
S1 u ⟨∙⟩ v & S1⇓ = S2 u v , refl
S2 u v ⟨∙⟩ w & S2⇓ uw⇓ vw⇓ uwvw⇓ with u ⟨∙⟩ w & uw⇓ | v ⟨∙⟩ w & vw⇓
... | u′ , refl | v′ , refl = u′ ⟨∙⟩ v′ & uwvw⇓
NE0 ⟨∙⟩ u & ()
Inl0 ⟨∙⟩ u & Inl0⇓ = Inl1 u , refl
Inr0 ⟨∙⟩ u & Inr0⇓ = Inr1 u , refl
C0 ⟨∙⟩ u & C0⇓ = C1 u , refl
C1 u ⟨∙⟩ v & C1⇓ = C2 u v , refl
C2 u v ⟨∙⟩ Inl1 w & C2l⇓ ⇓w′ = u ⟨∙⟩ w & ⇓w′
C2 u v ⟨∙⟩ Inr1 w & C2r⇓ ⇓w′ = v ⟨∙⟩ w & ⇓w′

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u
eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (A⇓ x⇓ y⇓ ⇓w) with eval x x⇓ | eval y y⇓
... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w
eval NE NE⇓ = NE0 , refl
eval Inl Inl⇓ = Inl0 , refl
eval Inr Inr⇓ = Inr0 , refl
eval C C⇓ = C0 , refl
