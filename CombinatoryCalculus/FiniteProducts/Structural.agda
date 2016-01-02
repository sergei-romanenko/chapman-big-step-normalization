module FiniteProducts.Structural where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep
open import FiniteProducts.StrongComp

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

eval : ∀ {α}(t : Tm α){n} → t ⇓ n → Σ (Nf α) λ n' → n' ≡ n
eval .K K⇓ = K0 , refl 
eval .S S⇓ = S0 , refl
eval ._ (A⇓ {x = t} {y = u} p q r) with eval t p | eval u q
... | f , refl | a , refl = f ⟨∙⟩ a & r
eval .void rvoid = voidⁿ , refl 
eval .pr rpr = prⁿ , refl 
eval .fst  rfst = fstⁿ , refl 
eval .snd  rsnd = sndⁿ , refl 

nf : ∀ {α} (x : Tm α) → Nf α
nf x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | u′ , u′≡u = u′

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝
complete x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl = x≈⌜u⌝
