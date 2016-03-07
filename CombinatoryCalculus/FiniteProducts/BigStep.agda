module FiniteProducts.BigStep where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax

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
  Pr0⇓ : ∀ {α β u} →
    Pr0 {α} {β} ⟨∙⟩ u ⇓ Pr1 u
  Pr1⇓ : ∀ {α β u v} →
    Pr1 {α} {β} u ⟨∙⟩ v ⇓ Pr2 u v
  Fst0⇓ : ∀ {α β u v} →
    Fst0 {α} {β} ⟨∙⟩ Pr2 u v ⇓ u
  Snd0⇓ : ∀ {α β u v} →
    Snd0 {α} {β} ⟨∙⟩ Pr2 u v ⇓ v

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  Void⇓ :
    Void ⇓ Void0
  Pr⇓ : ∀ {α β} →
    Pr {α} {β} ⇓ Pr0
  Fst⇓ : ∀ {α β} →
    Fst {α} {β} ⇓ Fst0
  Snd⇓ : ∀ {α β} →
    Snd {α} {β} ⇓ Snd0

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
Pr0 ⟨∙⟩ v & Pr0⇓ = Pr1 v , refl
Pr1 u ⟨∙⟩ v & Pr1⇓ = Pr2 u v , refl
Fst0 ⟨∙⟩ Pr2 u v & Fst0⇓ = u , refl
Snd0 ⟨∙⟩ Pr2 u v & Snd0⇓ = v , refl

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u

eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (A⇓ x⇓ y⇓ ⇓w)
  with eval x x⇓ | eval y y⇓
... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w
eval Void Void⇓ = Void0 , refl
eval Pr Pr⇓ = Pr0 , refl
eval Fst Fst⇓ = Fst0 , refl
eval Snd Snd⇓ = Snd0 , refl


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
⟨∙⟩⇓-det Pr0⇓ Pr0⇓ = refl
⟨∙⟩⇓-det Pr1⇓ Pr1⇓ = refl
⟨∙⟩⇓-det Fst0⇓ Fst0⇓ = refl
⟨∙⟩⇓-det Snd0⇓ Snd0⇓ = refl


⇓-det : ∀ {α} {x : Tm α} {u u′ : Nf α} →
  x ⇓ u → x ⇓ u′ → u ≡ u′
⇓-det K⇓ K⇓ = refl
⇓-det S⇓ S⇓ = refl
⇓-det (A⇓ p q r) (A⇓ p′ q′ r′)
  rewrite ⇓-det p p′ | ⇓-det q q′ | ⟨∙⟩⇓-det r r′
  = refl
⇓-det Void⇓ Void⇓ = refl
⇓-det Pr⇓ Pr⇓ = refl
⇓-det Fst⇓ Fst⇓ = refl
⇓-det Snd⇓ Snd⇓ = refl
