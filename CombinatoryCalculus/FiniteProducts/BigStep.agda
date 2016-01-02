module FiniteProducts.BigStep where
open import FiniteProducts.Syntax

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
  rprⁿ  : ∀ {α β}{x : Nf α} → prⁿ {β = β} ⟨∙⟩ x ⇓ prⁿ¹ x
  rprⁿ¹ : ∀ {α β}{x : Nf α}{y : Nf β} → prⁿ¹ x ⟨∙⟩ y ⇓ prⁿ² x y
  rfstⁿ : ∀ {α β}{x : Nf α}{y : Nf β} → fstⁿ ⟨∙⟩ prⁿ² x y ⇓ x
  rsndⁿ : ∀ {α β}{x : Nf α}{y : Nf β} → sndⁿ ⟨∙⟩ prⁿ² x y ⇓ y

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  rvoid : void ⇓ voidⁿ
  rpr  : ∀ {α β} → pr {α} {β} ⇓ prⁿ
  rfst : ∀ {α β} → fst {α} {β} ⇓ fstⁿ
  rsnd : ∀ {α β} → snd {α} {β} ⇓ sndⁿ