module FiniteCoproducts.Structural where
open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.BigStep
open import FiniteCoproducts.StrongComp

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

nf⁼ : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
nf⁼ .K K⇓ = K0 , refl 
nf⁼ .S S⇓ = S0 , refl
nf⁼ ._ (A⇓ {x = x} {y = y} p q r) with nf⁼ x p | nf⁼ y q
... | f , refl | a , refl = f ⟨∙⟩ a & r
nf⁼ .NE rNE = NEⁿ , refl 
nf⁼ .inl rinl = inlⁿ , refl
nf⁼ .inr rinr = inrⁿ , refl
nf⁼ .C rC = Cⁿ , refl 

nf : ∀ {α} → Tm α → Nf α
nf t = proj₁ (nf⁼ t (proj₁ (proj₂ (prop2 t))))
