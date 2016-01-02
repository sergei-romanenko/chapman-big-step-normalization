module BasicSystem.Structural where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep
open import BasicSystem.StrongComp

_⟨∙⟩_&_ : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α)
  {w} (uv⇓ : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w

K0 ⟨∙⟩ v & K0⇓ = K1 v , refl
K1 u ⟨∙⟩ v & K1⇓ = u , refl
S0 ⟨∙⟩ v & S0⇓ = S1 v , refl
S1 u ⟨∙⟩ v & S1⇓ = S2 u v , refl
S2 u v ⟨∙⟩ w & S2⇓ uw⇓ vw⇓ uwvw⇓ with u ⟨∙⟩ w & uw⇓ | v ⟨∙⟩ w & vw⇓
... | u′ , refl | v′ , refl = u′ ⟨∙⟩ v′ & uwvw⇓

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u

eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (A⇓ x⇓ y⇓ ⇓w) with eval x x⇓ | eval y y⇓
... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w

nf : ∀ {α} (x : Tm α) → Nf α
nf x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | u′ , u′≡u = u′

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝
complete x with prop2 x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl = x≈⌜u⌝
