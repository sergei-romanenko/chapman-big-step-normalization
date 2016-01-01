module FiniteCoproducts.Structural where
open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.BigStep
open import FiniteCoproducts.StrongComp

_∙∙⁼_&_ : ∀ {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} → f ∙ⁿ a ⇓ n →
          Σ (Nf τ) λ n' → n' ≡ n
.Kⁿ        ∙∙⁼ x & rKⁿ           = Kⁿ¹ x , refl 
.(Kⁿ¹ x)   ∙∙⁼ y & rKⁿ¹ {x = x}  = x ,  refl  
.Sⁿ        ∙∙⁼ x & rSⁿ           = Sⁿ¹ x , refl  
.(Sⁿ¹ x)   ∙∙⁼ y & rSⁿ¹ {x = x}  = Sⁿ² x y , refl  
.(Sⁿ² x y) ∙∙⁼ z & rSⁿ² {x = x}{y = y} p q r with x ∙∙⁼ z & p | y ∙∙⁼ z & q
... | u , refl | v , refl  = u ∙∙⁼ v & r 
.inlⁿ      ∙∙⁼ x & rinl          = inlⁿ¹ x , refl
.inrⁿ      ∙∙⁼ x & rinr          = inrⁿ¹ x , refl
.Cⁿ        ∙∙⁼ l  & rCⁿ          = Cⁿ¹ l , refl  
.(Cⁿ¹ l)   ∙∙⁼ r  & rCⁿ¹ {l = l} = Cⁿ² l r , refl  
.(Cⁿ² l r) ∙∙⁼ .(inlⁿ¹ x) & rCⁿ²ˡ {l = l}{r = r}{x = x} p = l ∙∙⁼ x & p
.(Cⁿ² l r) ∙∙⁼ .(inrⁿ¹ x) & rCⁿ²ʳ {l = l}{r = r}{x = x} p = r ∙∙⁼ x & p

nf⁼ : ∀ {σ}(t : Tm σ){n} → t ⇓ n → Σ (Nf σ) λ n' → n' ≡ n
nf⁼ .K rK = Kⁿ , refl 
nf⁼ .S rS = Sⁿ , refl
nf⁼ .(t ∙ u) (r∙ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | f , refl | a , refl = f ∙∙⁼ a & r
nf⁼ .NE rNE = NEⁿ , refl 
nf⁼ .inl rinl = inlⁿ , refl
nf⁼ .inr rinr = inrⁿ , refl
nf⁼ .C rC = Cⁿ , refl 

nf : ∀ {σ} → Tm σ → Nf σ
nf t = proj₁ (nf⁼ t (proj₁ (proj₂ (prop2 t))))
