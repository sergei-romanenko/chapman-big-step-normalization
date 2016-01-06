module FullSystem.BigStep where

open import FullSystem.Utils
open import FullSystem.Syntax

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
  Pr0⇓  : ∀ {α β}{x : Nf α} → Pr0 {β = β} ⟨∙⟩ x ⇓ Pr1 x
  Pr1⇓ : ∀ {α β}{x : Nf α}{y : Nf β} → Pr1 x ⟨∙⟩ y ⇓ Pr2 x y
  Fst0⇓ : ∀ {α β}{x : Nf α}{y : Nf β} → Fst0 ⟨∙⟩ Pr2 x y ⇓ x
  Snd0⇓ : ∀ {α β}{x : Nf α}{y : Nf β} → Snd0 ⟨∙⟩ Pr2 x y ⇓ y
  C0⇓    : ∀ {α β γ}{l : Nf (α ⇒ γ)} → C0 {β = β}  ⟨∙⟩ l ⇓ C1 l
  C1⇓   : ∀ {α β γ}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)} → 
           C1 l ⟨∙⟩ r ⇓ C2 l r
  C2L⇓  : {α β γ : Ty}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)}{x : Nf α}{y : Nf γ} →
           l ⟨∙⟩ x ⇓ y → C2 l r ⟨∙⟩ Inl1 x ⇓ y 
  C2R⇓  : {α β γ : Ty}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)}{x : Nf β}{y : Nf γ} →
           r ⟨∙⟩ x ⇓ y → C2 l r ⟨∙⟩ Inr1 x ⇓ y 
  Inl0⇓ : ∀ {α β}{x : Nf α} → Inl0 {β = β} ⟨∙⟩ x ⇓ Inl1 x
  Inr0⇓ : ∀ {α β}{x : Nf β} → Inr0 {α = α} ⟨∙⟩ x ⇓ Inr1 x
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
  Void⇓ : Void ⇓ Void0
  Pr⇓   : ∀ {α β} → Pr {α} {β} ⇓ Pr0
  Fst⇓  : ∀ {α β} → Fst {α} {β} ⇓ Fst0
  Snd⇓  : ∀ {α β} → Snd {α} {β} ⇓ Snd0
  NE⇓  : ∀ {α} → NE {α} ⇓ NE0
  Inl⇓ : ∀ {α β} → Inl {α}{β} ⇓ Inl0
  Inr⇓ : ∀ {α β} → Inr {α}{β} ⇓ Inr0
  C⇓   : ∀ {α β γ} → C {α} {β} {γ} ⇓ C0
  Zero⇓ : Zero ⇓ Zero0
  Suc⇓  : Suc ⇓ Suc0
  R⇓    : ∀ {α} → R {α} ⇓ R0

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
.Pr0       ⟨∙⟩ x & Pr0⇓           = Pr1 x , refl  
.(Pr1 x)  ⟨∙⟩ y & Pr1⇓ {x = x}  = Pr2 x y , refl  
.Fst0      ⟨∙⟩ (Pr2 x y) & Fst0⇓ = x , refl 
.Snd0      ⟨∙⟩ (Pr2 x y) & Snd0⇓ = y , refl 
.Inl0      ⟨∙⟩ x & Inl0⇓          = Inl1 x , refl
.Inr0      ⟨∙⟩ x & Inr0⇓          = Inr1 x , refl
.C0        ⟨∙⟩ l  & C0⇓          = C1 l , refl  
.(C1 l)   ⟨∙⟩ r  & C1⇓ {l = l} = C2 l r , refl  
.(C2 l r) ⟨∙⟩ .(Inl1 x) & C2L⇓ {l = l}{r = r}{x = x} p = l ⟨∙⟩ x & p
.(C2 l r) ⟨∙⟩ .(Inr1 x) & C2R⇓ {l = l}{r = r}{x = x} p = r ⟨∙⟩ x & p
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
eval .Void Void⇓ = Void0 , refl 
eval .Pr Pr⇓ = Pr0 , refl 
eval .Fst  Fst⇓ = Fst0 , refl 
eval .Snd  Snd⇓ = Snd0 , refl 
eval .NE NE⇓ = NE0 , refl 
eval .Inl Inl⇓ = Inl0 , refl
eval .Inr Inr⇓ = Inr0 , refl
eval .C C⇓ = C0 , refl 
eval .Zero Zero⇓ = Zero0 , refl 
eval .Suc Suc⇓   = Suc0 , refl 
eval .R R⇓       = R0 , refl 
