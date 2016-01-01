module NaturalNumbers.Structural where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep
open import NaturalNumbers.StrongComp

_∙∙⁼_&_ : ∀ {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} → f ∙ⁿ a ⇓ n →
          Σ (Nf τ) λ n' → n' ≡ n
.Kⁿ        ∙∙⁼ x & rKⁿ          = Kⁿ¹ x , refl
.(Kⁿ¹ x)   ∙∙⁼ y & rKⁿ¹ {x = x} = x , refl
.Sⁿ        ∙∙⁼ x & rSⁿ          = Sⁿ¹ x , refl
.(Sⁿ¹ x)   ∙∙⁼ y & rSⁿ¹ {x = x} = Sⁿ² x y , refl
.(Sⁿ² x y) ∙∙⁼ z & rSⁿ² {x = x}{y = y} p q r with x ∙∙⁼ z & p | y ∙∙⁼ z & q
... | u , refl | v , refl = u ∙∙⁼ v & r 
.sucⁿ      ∙∙⁼ n & rsucⁿ        = sucⁿ¹ n , refl
.Rⁿ        ∙∙⁼ z & rRⁿ          = Rⁿ¹ z , refl
.(Rⁿ¹ z)   ∙∙⁼ f & rRⁿ¹ {z = z} = Rⁿ² z f , refl
.(Rⁿ² z f) ∙∙⁼ .zeroⁿ     & rRⁿ²z {z = z}{f = f} = z , refl
.(Rⁿ² z f) ∙∙⁼ .(sucⁿ¹ n) & rRⁿ²f {z = z}{f = f}{n = n} p q r
  with f ∙∙⁼ n & p | Rⁿ² z f ∙∙⁼ n & q
... | fn , refl | rn , refl = fn ∙∙⁼ rn & r 

nf⁼ : ∀ {σ}(t : Tm σ){n} → t ⇓ n → Σ (Nf σ) λ n' → n' ≡ n
nf⁼ .K rK = Kⁿ , refl 
nf⁼ .S rS = Sⁿ , refl
nf⁼ .(t ∙ u) (r∙ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | f , refl | a , refl = f ∙∙⁼ a & r
nf⁼ .zero rzero = zeroⁿ , refl 
nf⁼ .suc rsuc   = sucⁿ , refl 
nf⁼ .R rR       = Rⁿ , refl 

nf : ∀ {σ} → Tm σ → Nf σ
nf t = proj₁ (nf⁼ t (proj₁ (proj₂ (prop2 t))))
