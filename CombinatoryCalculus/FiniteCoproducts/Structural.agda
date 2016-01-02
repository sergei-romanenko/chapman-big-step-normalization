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

eval : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
eval .K K⇓ = K0 , refl 
eval .S S⇓ = S0 , refl
eval ._ (A⇓ {x = x} {y = y} p q r) with eval x p | eval y q
... | f , refl | a , refl = f ⟨∙⟩ a & r
eval .NE rNE = NEⁿ , refl 
eval .inl rinl = inlⁿ , refl
eval .inr rinr = inrⁿ , refl
eval .C rC = Cⁿ , refl 

nf : ∀ {α} (x : Tm α) → Nf α
nf x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | u′ , u′≡u = u′

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝
complete x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl = x≈⌜u⌝
