module BasicSystem.Structural where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep
open import BasicSystem.StrongComp

_∙∙⁼_&_ : ∀ {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} → f ∙ⁿ a ⇓ n →
          Σ (Nf τ) λ n' → n' ≡ n
.Kⁿ        ∙∙⁼ x & rKⁿ          = Kⁿ¹ x , refl 
.(Kⁿ¹ x)   ∙∙⁼ y & rKⁿ¹ {x = x} = x , refl  
.Sⁿ        ∙∙⁼ x & rSⁿ          = Sⁿ¹ x , refl  
.(Sⁿ¹ x)   ∙∙⁼ y & rSⁿ¹ {x = x} = Sⁿ² x y , refl  
.(Sⁿ² x y) ∙∙⁼ z & rSⁿ² {x = x}{y = y} p q r with x ∙∙⁼ z & p | y ∙∙⁼ z & q
... | u , refl | v , refl = u ∙∙⁼ v & r 

nf⁼ : ∀ {σ}(t : Tm σ){n} → t ⇓ n → Σ (Nf σ) λ n' → n' ≡ n
nf⁼ .K rK = Kⁿ , refl 
nf⁼ .S rS = Sⁿ , refl
nf⁼ .(t ∙ u) (r∙ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | f , refl | a , refl = f ∙∙⁼ a & r

nf : ∀ {σ} → Tm σ → Nf σ
nf t = proj₁ (nf⁼ t (π₀ (proj₂ (prop2 t))))

complete : ∀ {σ}(t : Tm σ) → t ≈ ⌜ nf t ⌝ 
complete t with nf⁼ t (π₀ (proj₂ (prop2 t)))
... | (._ , refl) = π₂ (proj₂(prop2 t)) 
