module FiniteProducts.BigStep where
open import FiniteProducts.Syntax

-- Big step semantics (the graph of the recursive function)
data _$ⁿ_⇓_ : {σ τ : Ty} → Nf (σ ⇒ τ) → Nf σ → Nf τ → Set where
  rKⁿ  : {σ τ : Ty}{x : Nf σ} → Kⁿ {σ} {τ} $ⁿ x ⇓ Kⁿ¹ x
  rKⁿ¹ : {σ τ : Ty}{x : Nf σ} → {y : Nf τ} → Kⁿ¹ x $ⁿ y ⇓ x
  rSⁿ  : {σ τ ρ : Ty} {x : Nf (σ ⇒ τ ⇒ ρ)} → Sⁿ $ⁿ x ⇓ Sⁿ¹ x
  rSⁿ¹ : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)} → 
         Sⁿ¹ x $ⁿ y ⇓ Sⁿ² x y
  rSⁿ² : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)}{z : Nf σ}
         {u : Nf (τ ⇒ ρ)} → x $ⁿ z ⇓ u → {v : Nf τ} → y $ⁿ z ⇓ v → 
         {w : Nf ρ} → u $ⁿ v ⇓ w → Sⁿ² x y $ⁿ z ⇓ w 
  rprⁿ  : ∀ {σ τ}{x : Nf σ} → prⁿ {τ = τ} $ⁿ x ⇓ prⁿ¹ x
  rprⁿ¹ : ∀ {σ τ}{x : Nf σ}{y : Nf τ} → prⁿ¹ x $ⁿ y ⇓ prⁿ² x y
  rfstⁿ : ∀ {σ τ}{x : Nf σ}{y : Nf τ} → fstⁿ $ⁿ prⁿ² x y ⇓ x
  rsndⁿ : ∀ {σ τ}{x : Nf σ}{y : Nf τ} → sndⁿ $ⁿ prⁿ² x y ⇓ y

data _⇓_ : {σ : Ty} → Tm σ → Nf σ → Set where
  rK    : {σ τ : Ty} → K {σ} {τ} ⇓ Kⁿ
  rS    : {σ τ ρ : Ty} → S {σ} {τ} {ρ} ⇓ Sⁿ
  r$    : ∀ {σ τ}{t : Tm (σ ⇒ τ)}{f} → t ⇓ f → {u : Tm σ}
          {a : Nf σ} → u ⇓ a → {v : Nf τ} → f $ⁿ a ⇓ v  → (t $ u) ⇓ v
  rvoid : void ⇓ voidⁿ
  rpr   : ∀ {σ τ} → pr {σ} {τ} ⇓ prⁿ
  rfst  : ∀ {σ τ} → fst {σ} {τ} ⇓ fstⁿ
  rsnd  : ∀ {σ τ} → snd {σ} {τ} ⇓ sndⁿ