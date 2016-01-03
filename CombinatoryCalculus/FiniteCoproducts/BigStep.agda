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
  rCⁿ    : ∀ {α β γ}{l : Nf (α ⇒ γ)} → Cⁿ {β = β}  ⟨∙⟩ l ⇓ Cⁿ¹ l
  rCⁿ¹   : ∀ {α β γ}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)} → 
           Cⁿ¹ l ⟨∙⟩ r ⇓ Cⁿ² l r
  rCⁿ²ˡ  : {α β γ : Ty}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)}{x : Nf α}{y : Nf γ} →
           l ⟨∙⟩ x ⇓ y → Cⁿ² l r ⟨∙⟩ inlⁿ¹ x ⇓ y 
  rCⁿ²ʳ  : {α β γ : Ty}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)}{x : Nf β}{y : Nf γ} →
           r ⟨∙⟩ x ⇓ y → Cⁿ² l r ⟨∙⟩ inrⁿ¹ x ⇓ y 
  rinl : ∀ {α β}{x : Nf α} → inlⁿ {β = β} ⟨∙⟩ x ⇓ inlⁿ¹ x
  rinr : ∀ {α β}{x : Nf β} → inrⁿ {α = α} ⟨∙⟩ x ⇓ inrⁿ¹ x

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  rNE  : ∀ {α} → NE {α} ⇓ NEⁿ
  rinl : ∀ {α β} → inl {α}{β} ⇓ inlⁿ
  rinr : ∀ {α β} → inr {α}{β} ⇓ inrⁿ
  rC   : ∀ {α β γ} → C {α} {β} {γ} ⇓ Cⁿ

--
-- Structurally recursive normalizer.
--

_⟨∙⟩_&_ : ∀ {α β}(f : Nf (α ⇒ β))(a : Nf α){n} → f ⟨∙⟩ a ⇓ n →
          Σ (Nf β) λ n' → n' ≡ n
.K0        ⟨∙⟩ x & K0⇓           = K1 x , refl 
.(K1 x)   ⟨∙⟩ y & K1⇓ {u = x}  = x ,  refl  
.S0        ⟨∙⟩ x & S0⇓           = S1 x , refl  
.(S1 x)   ⟨∙⟩ y & S1⇓ {u = x}  = S2 x y , refl  
.(S2 x y) ⟨∙⟩ z & S2⇓ {u = x}{v = y} p q r with x ⟨∙⟩ z & p | y ⟨∙⟩ z & q
... | u , refl | v , refl  = u ⟨∙⟩ v & r 
.inlⁿ      ⟨∙⟩ x & rinl          = inlⁿ¹ x , refl
.inrⁿ      ⟨∙⟩ x & rinr          = inrⁿ¹ x , refl
.Cⁿ        ⟨∙⟩ l  & rCⁿ          = Cⁿ¹ l , refl  
.(Cⁿ¹ l)   ⟨∙⟩ r  & rCⁿ¹ {l = l} = Cⁿ² l r , refl  
.(Cⁿ² l r) ⟨∙⟩ .(inlⁿ¹ x) & rCⁿ²ˡ {l = l}{r = r}{x = x} p = l ⟨∙⟩ x & p
.(Cⁿ² l r) ⟨∙⟩ .(inrⁿ¹ x) & rCⁿ²ʳ {l = l}{r = r}{x = x} p = r ⟨∙⟩ x & p

eval : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
eval .K K⇓ = K0 , refl 
eval .S S⇓ = S0 , refl
eval ._ (A⇓ {x = x} {y = y} p q r) with eval x p | eval y q
... | f , refl | a , refl = f ⟨∙⟩ a & r
eval .NE rNE = NEⁿ , refl 
eval .inl rinl = inlⁿ , refl
eval .inr rinr = inrⁿ , refl
eval .C rC = Cⁿ , refl 
