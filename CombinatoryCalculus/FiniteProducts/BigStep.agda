module FiniteProducts.BigStep where

open import FiniteProducts.Utils
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

--
-- Structurally recursive normalizer.
--

_⟨∙⟩_&_ : ∀ {α β}(f : Nf (α ⇒ β))(a : Nf α){n} → f ⟨∙⟩ a ⇓ n →
          Σ (Nf β) λ n' → n' ≡ n
.K0        ⟨∙⟩ x & K0⇓            = K1 x , refl 
.(K1 x)   ⟨∙⟩ y & K1⇓ {u = x}   = x ,  refl  
.S0        ⟨∙⟩ x & S0⇓            = S1 x , refl  
.(S1 x)   ⟨∙⟩ y & S1⇓ {u = x}   = S2 x y , refl  
.(S2 x y) ⟨∙⟩ z & S2⇓ {u = x}{v = y} p q r with x ⟨∙⟩ z & p | y ⟨∙⟩ z & q
... | u , refl | v , refl = u ⟨∙⟩ v & r 
.prⁿ       ⟨∙⟩ x & rprⁿ           = prⁿ¹ x , refl  
.(prⁿ¹ x)  ⟨∙⟩ y & rprⁿ¹ {x = x}  = prⁿ² x y , refl  
.fstⁿ      ⟨∙⟩ (prⁿ² x y) & rfstⁿ = x , refl 
.sndⁿ      ⟨∙⟩ (prⁿ² x y) & rsndⁿ = y , refl 

eval : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
eval .K K⇓ = K0 , refl 
eval .S S⇓ = S0 , refl
eval ._ (A⇓ {x = t} {y = u} p q r) with eval t p | eval u q
... | f , refl | a , refl = f ⟨∙⟩ a & r
eval .void rvoid = voidⁿ , refl 
eval .pr rpr = prⁿ , refl 
eval .fst  rfst = fstⁿ , refl 
eval .snd  rsnd = sndⁿ , refl 
