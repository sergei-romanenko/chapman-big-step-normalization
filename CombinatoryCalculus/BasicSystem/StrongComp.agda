module BasicSystem.StrongComp where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set
SCN {⋆} u = ⊤
SCN {α ⇒ β} u =
  ∀ v → SCN v → ∃ λ w → (u ⟨∙⟩ v ⇓ w) × (⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝) × SCN w

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u
--

all-scn-K2 : ∀ {α β} u (p : SCN u) v (q : SCN v) →
  ∃ λ w → K1 {α} {β} u ⟨∙⟩ v ⇓ w × K ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝ × SCN w
all-scn-K2 u p v q =
  u , K1⇓ , ≈K , p

all-scn-K1 : ∀ {α β} u (p : SCN u) →
  ∃ λ w → K0 {α} {β} ⟨∙⟩ u ⇓ w × K ∙ ⌜ u ⌝ ≈ ⌜ w ⌝  × SCN w
all-scn-K1 u p =
  K1 u , K0⇓ , ≈refl , all-scn-K2 u p

all-scn-S3 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) w (r : SCN w) →
  ∃ λ w′ → S2 {α} {β} {γ} u v ⟨∙⟩ w ⇓ w′ ×
    S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝ ≈ ⌜ w′ ⌝ × SCN w′

all-scn-S3 u p v q w r with p w r | q w r
... | w₁ , ⇓w₁ , ≈w₁ , r₁ | w₂ , ⇓w₂ , ≈w₂ , r₂ with r₁ w₂ r₂
... | w₃ , ⇓w₃ , ≈w₃ , r₃ =
  w₃ , S2⇓ ⇓w₁ ⇓w₂ ⇓w₃ , ≈⌜w₃⌝ , r₃
  where
  open ≈-Reasoning
  ≈⌜w₃⌝ : S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝ ≈ ⌜ w₃ ⌝
  ≈⌜w₃⌝ = begin
    S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝
      ≈⟨ ≈S ⟩
    (⌜ u ⌝ ∙ ⌜ w ⌝) ∙ (⌜ v ⌝ ∙ ⌜ w ⌝)
      ≈⟨ ≈cong∙ ≈w₁ ≈w₂ ⟩
    ⌜ w₁ ⌝ ∙ ⌜ w₂ ⌝
      ≈⟨ ≈w₃ ⟩
    ⌜ w₃ ⌝
    ∎

all-scn-S2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  ∃ λ w → S1 {α} {β} {γ} u ⟨∙⟩ v ⇓ w × S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝ × SCN w
all-scn-S2 u p v q =
  S2 u v , S1⇓ , ≈refl , all-scn-S3 u p v q

all-scn-S1 : ∀ {α β γ} u (p : SCN u) →
  ∃ λ w → S0 {α} {β} {γ} ⟨∙⟩ u ⇓ w × S ∙ ⌜ u ⌝ ≈ ⌜ w ⌝ × SCN w
all-scn-S1 u p =
  S1 u , S0⇓ , ≈refl , all-scn-S2 u p

-- ∀ {α} (u : Nf α) → SCN u

all-scn : ∀ {α} (u : Nf α) → SCN u

all-scn K0 =
  all-scn-K1
all-scn (K1 u) =
  all-scn-K2 u (all-scn u)
all-scn S0 =
  all-scn-S1
all-scn (S1 u) =
  all-scn-S2 u (all-scn u)
all-scn (S2 u v) =
  all-scn-S3 u (all-scn u) v (all-scn v)

--
-- "Strong computability" on terms.
--

SC : ∀ {α} (x : Tm α) → Set
SC x = ∃ λ u → (x ⇓ u) × (x ≈ ⌜ u ⌝) × SCN u

--
-- All terms are strongly computable!
--    ∀ {α} (x : Tm α) → SC u
--

all-sc : ∀ {α} (x : Tm α) → SC x

all-sc K =
  K0 , K⇓ , ≈refl , all-scn-K1
all-sc S =
  S0 , S⇓ , ≈refl , all-scn-S1
all-sc (x ∙ y) with all-sc x | all-sc y
... | u , ⇓u , ≈⌜u⌝ , p | v , ⇓v , ≈⌜v⌝ , q with p v q
... | w , ⇓w , ≈⌜w⌝ , r =
  w , A⇓ ⇓u ⇓v ⇓w , x∙y≈⌜w⌝ , r
  where
  x∙y≈⌜w⌝ :  x ∙ y ≈ ⌜ w ⌝
  x∙y≈⌜w⌝ = begin
    x ∙ y
      ≈⟨ ≈cong∙ ≈⌜u⌝ ≈⌜v⌝  ⟩
    ⌜ u ⌝ ∙ ⌜ v ⌝
      ≈⟨ ≈⌜w⌝ ⟩
    ⌜ w ⌝
    ∎
    where open ≈-Reasoning
