module BasicSystem.Structural where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep
open import BasicSystem.StrongComp

_⟨∙⟩_&_ : ∀ {α β}(f : Nf (α ⇒ β))(a : Nf α){n} → f ⟨∙⟩ a ⇓ n →
          Σ (Nf β) λ n' → n' ≡ n
.K0        ⟨∙⟩ x & K0⇓          = K1 x , refl 
.(K1 u)   ⟨∙⟩ y & K1⇓ {u = u} = u , refl  
.S0        ⟨∙⟩ x & S0⇓          = S1 x , refl  
.(S1 u)   ⟨∙⟩ y & S1⇓ {u = u} = S2 u y , refl  
.(S2 u v) ⟨∙⟩ w & S2⇓ {u = u} {v = v} p q r with u ⟨∙⟩ w & p | v ⟨∙⟩ w & q
... | u′ , refl | v′ , refl = u′ ⟨∙⟩ v′ & r 

nf⁼ : ∀ {α} (x : Tm α) {u} (x⇓u : x ⇓ u) → ∃ λ u′ → u′ ≡ u
nf⁼ .K K⇓ = K0 , refl
nf⁼ .S S⇓ = S0 , refl
nf⁼ ._ (A⇓ {x = x} {y = y} x⇓u y⇓v ⇓w) with nf⁼ x x⇓u | nf⁼ y y⇓v
... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w

nf : ∀ {α} → Tm α → Nf α
nf t = proj₁ (nf⁼ t (proj₁ (proj₂ (prop2 t))))

complete : ∀ {α}(t : Tm α) → t ≈ ⌜ nf t ⌝ 
complete t with nf⁼ t (proj₁ (proj₂ (prop2 t)))
... | (._ , refl) = (proj₂ ∘ proj₂) (proj₂(prop2 t)) 
