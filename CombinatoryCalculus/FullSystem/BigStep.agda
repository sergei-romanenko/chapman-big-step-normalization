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
  rprⁿ  : ∀ {α β}{x : Nf α} → prⁿ {β = β} ⟨∙⟩ x ⇓ prⁿ¹ x
  rprⁿ¹ : ∀ {α β}{x : Nf α}{y : Nf β} → prⁿ¹ x ⟨∙⟩ y ⇓ prⁿ² x y
  rfstⁿ : ∀ {α β}{x : Nf α}{y : Nf β} → fstⁿ ⟨∙⟩ prⁿ² x y ⇓ x
  rsndⁿ : ∀ {α β}{x : Nf α}{y : Nf β} → sndⁿ ⟨∙⟩ prⁿ² x y ⇓ y
  rCⁿ    : ∀ {α β γ}{l : Nf (α ⇒ γ)} → Cⁿ {β = β}  ⟨∙⟩ l ⇓ Cⁿ¹ l
  rCⁿ¹   : ∀ {α β γ}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)} → 
           Cⁿ¹ l ⟨∙⟩ r ⇓ Cⁿ² l r
  rCⁿ²ˡ  : {α β γ : Ty}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)}{x : Nf α}{y : Nf γ} →
           l ⟨∙⟩ x ⇓ y → Cⁿ² l r ⟨∙⟩ inlⁿ¹ x ⇓ y 
  rCⁿ²ʳ  : {α β γ : Ty}{l : Nf (α ⇒ γ)}{r : Nf (β ⇒ γ)}{x : Nf β}{y : Nf γ} →
           r ⟨∙⟩ x ⇓ y → Cⁿ² l r ⟨∙⟩ inrⁿ¹ x ⇓ y 
  rinl : ∀ {α β}{x : Nf α} → inlⁿ {β = β} ⟨∙⟩ x ⇓ inlⁿ¹ x
  rinr : ∀ {α β}{x : Nf β} → inrⁿ {α = α} ⟨∙⟩ x ⇓ inrⁿ¹ x
  rsucⁿ : {n : Nf N} → sucⁿ ⟨∙⟩ n ⇓ sucⁿ¹ n
  rRⁿ   : {α : Ty}{z : Nf α} → Rⁿ ⟨∙⟩ z ⇓ Rⁿ¹ z
  rRⁿ¹  : {α : Ty}{z : Nf α}{f : Nf (N ⇒ α ⇒ α)} → Rⁿ¹ z ⟨∙⟩ f ⇓ Rⁿ² z f
  rRⁿ²z : {α : Ty}{z : Nf α}{f : Nf (N ⇒ α ⇒ α)} → 
          Rⁿ² z f ⟨∙⟩ zeroⁿ ⇓ z
  rRⁿ²f : {α : Ty}{z : Nf α}{f : Nf (N ⇒ α ⇒ α)}{n : Nf N}
          {fn : Nf (α ⇒ α)} → f ⟨∙⟩ n ⇓ fn → 
          {rn : Nf α} → Rⁿ² z f ⟨∙⟩ n ⇓ rn → 
          {rsn : Nf α} → fn ⟨∙⟩ rn ⇓ rsn → Rⁿ² z f ⟨∙⟩ sucⁿ¹ n ⇓ rsn

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ} →
    S {α} {β} {γ} ⇓ S0
  A⇓ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α} {u v w}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w)  →
    x ∙ y ⇓ w
  rvoid : void ⇓ voidⁿ
  rpr   : ∀ {α β} → pr {α} {β} ⇓ prⁿ
  rfst  : ∀ {α β} → fst {α} {β} ⇓ fstⁿ
  rsnd  : ∀ {α β} → snd {α} {β} ⇓ sndⁿ
  rNE  : ∀ {α} → NE {α} ⇓ NEⁿ
  rinl : ∀ {α β} → inl {α}{β} ⇓ inlⁿ
  rinr : ∀ {α β} → inr {α}{β} ⇓ inrⁿ
  rC   : ∀ {α β γ} → C {α} {β} {γ} ⇓ Cⁿ
  rzero : zero ⇓ zeroⁿ
  rsuc  : suc ⇓ sucⁿ
  rR    : ∀ {α} → R {α} ⇓ Rⁿ

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
.inlⁿ      ⟨∙⟩ x & rinl          = inlⁿ¹ x , refl
.inrⁿ      ⟨∙⟩ x & rinr          = inrⁿ¹ x , refl
.Cⁿ        ⟨∙⟩ l  & rCⁿ          = Cⁿ¹ l , refl  
.(Cⁿ¹ l)   ⟨∙⟩ r  & rCⁿ¹ {l = l} = Cⁿ² l r , refl  
.(Cⁿ² l r) ⟨∙⟩ .(inlⁿ¹ x) & rCⁿ²ˡ {l = l}{r = r}{x = x} p = l ⟨∙⟩ x & p
.(Cⁿ² l r) ⟨∙⟩ .(inrⁿ¹ x) & rCⁿ²ʳ {l = l}{r = r}{x = x} p = r ⟨∙⟩ x & p
.sucⁿ      ⟨∙⟩ n & rsucⁿ        = sucⁿ¹ n , refl  
.Rⁿ        ⟨∙⟩ z & rRⁿ          = Rⁿ¹ z , refl  
.(Rⁿ¹ z)   ⟨∙⟩ f & rRⁿ¹ {z = z} = Rⁿ² z f , refl 
.(Rⁿ² z f) ⟨∙⟩ .zeroⁿ     & rRⁿ²z {z = z}{f = f} = z , refl 
.(Rⁿ² z f) ⟨∙⟩ .(sucⁿ¹ n) & rRⁿ²f {z = z}{f = f}{n = n} p q r
  with f ⟨∙⟩ n & p | Rⁿ² z f ⟨∙⟩ n & q
... | fn , refl | rn , refl = fn ⟨∙⟩ rn & r 

eval : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
eval .K K⇓ = K0 , refl 
eval .S S⇓ = S0 , refl
eval .(t ∙ u) (A⇓ {x = t} {y = u} p q r) with eval t p | eval u q
... | f , refl | a , refl = f ⟨∙⟩ a & r
eval .void rvoid = voidⁿ , refl 
eval .pr rpr = prⁿ , refl 
eval .fst  rfst = fstⁿ , refl 
eval .snd  rsnd = sndⁿ , refl 
eval .NE rNE = NEⁿ , refl 
eval .inl rinl = inlⁿ , refl
eval .inr rinr = inrⁿ , refl
eval .C rC = Cⁿ , refl 
eval .zero rzero = zeroⁿ , refl 
eval .suc rsuc   = sucⁿ , refl 
eval .R rR       = Rⁿ , refl 
