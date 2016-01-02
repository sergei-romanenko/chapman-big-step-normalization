module FullSystem.Structural where
open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.BigStep
open import FullSystem.StrongComp

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

nf⁼ : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
nf⁼ .K K⇓ = K0 , refl 
nf⁼ .S S⇓ = S0 , refl
nf⁼ .(t ∙ u) (A⇓ {x = t} {y = u} p q r) with nf⁼ t p | nf⁼ u q
... | f , refl | a , refl = f ⟨∙⟩ a & r
nf⁼ .void rvoid = voidⁿ , refl 
nf⁼ .pr rpr = prⁿ , refl 
nf⁼ .fst  rfst = fstⁿ , refl 
nf⁼ .snd  rsnd = sndⁿ , refl 
nf⁼ .NE rNE = NEⁿ , refl 
nf⁼ .inl rinl = inlⁿ , refl
nf⁼ .inr rinr = inrⁿ , refl
nf⁼ .C rC = Cⁿ , refl 
nf⁼ .zero rzero = zeroⁿ , refl 
nf⁼ .suc rsuc   = sucⁿ , refl 
nf⁼ .R rR       = Rⁿ , refl 

nf : ∀ {α} → Tm α → Nf α
nf t = proj₁ (nf⁼ t (proj₁ (proj₂ (prop2 t))))
