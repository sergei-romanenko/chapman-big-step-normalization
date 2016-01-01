module FiniteProducts.Structural where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep
open import FiniteProducts.StrongComp

_∙∙⁼_&_ : ∀ {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} → f ∙ⁿ a ⇓ n →
          Σ (Nf τ) λ n' → n' ≡ n
.Kⁿ        ∙∙⁼ x & rKⁿ            = Kⁿ¹ x , refl 
.(Kⁿ¹ x)   ∙∙⁼ y & rKⁿ¹ {x = x}   = x ,  refl  
.Sⁿ        ∙∙⁼ x & rSⁿ            = Sⁿ¹ x , refl  
.(Sⁿ¹ x)   ∙∙⁼ y & rSⁿ¹ {x = x}   = Sⁿ² x y , refl  
.(Sⁿ² x y) ∙∙⁼ z & rSⁿ² {x = x}{y = y} p q r with x ∙∙⁼ z & p | y ∙∙⁼ z & q
... | u , refl | v , refl = u ∙∙⁼ v & r 
.prⁿ       ∙∙⁼ x & rprⁿ           = prⁿ¹ x , refl  
.(prⁿ¹ x)  ∙∙⁼ y & rprⁿ¹ {x = x}  = prⁿ² x y , refl  
.fstⁿ      ∙∙⁼ (prⁿ² x y) & rfstⁿ = x , refl 
.sndⁿ      ∙∙⁼ (prⁿ² x y) & rsndⁿ = y , refl 

nf⁼ : ∀ {σ}(t : Tm σ){n} → t ⇓ n → Σ (Nf σ) λ n' → n' ≡ n
nf⁼ .K rK = Kⁿ , refl 
nf⁼ .S rS = Sⁿ , refl
nf⁼ .(t ∙ u) (r∙ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | f , refl | a , refl = f ∙∙⁼ a & r
nf⁼ .void rvoid = voidⁿ , refl 
nf⁼ .pr rpr = prⁿ , refl 
nf⁼ .fst  rfst = fstⁿ , refl 
nf⁼ .snd  rsnd = sndⁿ , refl 

nf : ∀ {σ} → Tm σ → Nf σ
nf t = proj₁ (nf⁼ t (proj₁ (proj₂ (prop2 t))))
