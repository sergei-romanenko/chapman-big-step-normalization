module NaturalNumbers.BigStep where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax

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
  Suc0⇓ : {n : Nf N} → Suc0 ⟨∙⟩ n ⇓ Suc1 n
  R0⇓  : {α : Ty}{z : Nf α} → R0 ⟨∙⟩ z ⇓ R1 z
  R1⇓  : {α : Ty}{z : Nf α}{f : Nf (N ⇒ α ⇒ α)} → R1 z ⟨∙⟩ f ⇓ R2 z f
  R2Z⇓ : {α : Ty}{z : Nf α}{f : Nf (N ⇒ α ⇒ α)} → 
          R2 z f ⟨∙⟩ Zero0 ⇓ z
  R2S⇓ : {α : Ty}{z : Nf α}{f : Nf (N ⇒ α ⇒ α)}{n : Nf N}
          {fn : Nf (α ⇒ α)} → f ⟨∙⟩ n ⇓ fn → 
          {rn : Nf α} → R2 z f ⟨∙⟩ n ⇓ rn → 
          {rsn : Nf α} → fn ⟨∙⟩ rn ⇓ rsn → R2 z f ⟨∙⟩ Suc1 n ⇓ rsn

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  Zero⇓ : Zero ⇓ Zero0
  Suc⇓  : Suc ⇓ Suc0
  R⇓    : ∀ {α} → R {α} ⇓ R0


--
-- Structurally recursive normalizer.
--

_⟨∙⟩_&_ : ∀ {α β}(f : Nf (α ⇒ β))(a : Nf α){n} → f ⟨∙⟩ a ⇓ n →
          Σ (Nf β) λ n' → n' ≡ n
.K0        ⟨∙⟩ x & K0⇓          = K1 x , refl
.(K1 x)   ⟨∙⟩ y & K1⇓ {u = x} = x , refl
.S0        ⟨∙⟩ x & S0⇓          = S1 x , refl
.(S1 x)   ⟨∙⟩ y & S1⇓ {u = x} = S2 x y , refl
.(S2 x y) ⟨∙⟩ z & S2⇓ {u = x}{v = y} p q r with x ⟨∙⟩ z & p | y ⟨∙⟩ z & q
... | u , refl | v , refl = u ⟨∙⟩ v & r 
.Suc0      ⟨∙⟩ n & Suc0⇓        = Suc1 n , refl
.R0        ⟨∙⟩ z & R0⇓          = R1 z , refl
.(R1 z)   ⟨∙⟩ f & R1⇓ {z = z} = R2 z f , refl
.(R2 z f) ⟨∙⟩ .Zero0     & R2Z⇓ {z = z}{f = f} = z , refl
.(R2 z f) ⟨∙⟩ .(Suc1 n) & R2S⇓ {z = z}{f = f}{n = n} p q r
  with f ⟨∙⟩ n & p | R2 z f ⟨∙⟩ n & q
... | fn , refl | rn , refl = fn ⟨∙⟩ rn & r 

eval : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
eval .K K⇓ = K0 , refl 
eval .S S⇓ = S0 , refl
eval .(t ∙ u) (A⇓ {x = t} {y = u} p q r) with eval t p | eval u q
... | f , refl | a , refl = f ⟨∙⟩ a & r
eval .Zero Zero⇓ = Zero0 , refl 
eval .Suc Suc⇓   = Suc0 , refl 
eval .R R⇓       = R0 , refl 
