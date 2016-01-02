module NaturalNumbers.Structural where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep
open import NaturalNumbers.StrongComp

_⟨∙⟩_&_ : ∀ {α β}(f : Nf (α ⇒ β))(a : Nf α){n} → f ⟨∙⟩ a ⇓ n →
          Σ (Nf β) λ n' → n' ≡ n
.K0        ⟨∙⟩ x & K0⇓          = K1 x , refl
.(K1 x)   ⟨∙⟩ y & K1⇓ {u = x} = x , refl
.S0        ⟨∙⟩ x & S0⇓          = S1 x , refl
.(S1 x)   ⟨∙⟩ y & S1⇓ {u = x} = S2 x y , refl
.(S2 x y) ⟨∙⟩ z & S2⇓ {u = x}{v = y} p q r with x ⟨∙⟩ z & p | y ⟨∙⟩ z & q
... | u , refl | v , refl = u ⟨∙⟩ v & r 
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
eval .zero rzero = zeroⁿ , refl 
eval .suc rsuc   = sucⁿ , refl 
eval .R rR       = Rⁿ , refl 

nf : ∀ {α} (x : Tm α) → Nf α
nf x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | u′ , u′≡u = u′

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝
complete x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl = x≈⌜u⌝
