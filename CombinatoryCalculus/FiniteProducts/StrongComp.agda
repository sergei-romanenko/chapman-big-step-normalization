module FiniteProducts.StrongComp where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set
SCN {⋆} u = ⊤
SCN {α ⇒ β} u = ∀ v → SCN v →
  ∃ λ w → (u ⟨∙⟩ v ⇓ w) × (⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝) × SCN w
SCN {One} u = ⊤
SCN {α * β} u =
  (∃ λ w → (Fst0 ⟨∙⟩ u ⇓ w) × (Fst ∙ ⌜ u ⌝ ≈ ⌜ w ⌝) × SCN w)
  ×
  (∃ λ w → (Snd0 ⟨∙⟩ u ⇓ w) × (Snd ∙ ⌜ u ⌝ ≈ ⌜ w ⌝) × SCN w)

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u
--

all-scn-K1 : ∀ {α β} u (p : SCN u) → SCN (K1 {α} {β} u)
all-scn-K1 u p v q =
  u , K1⇓ , ≈K , p

all-scn-K0 : ∀ {α β} → SCN (K0 {α} {β})
all-scn-K0 u p =
  K1 u , K0⇓ , ≈refl , all-scn-K1 u p

all-scn-S2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  SCN (S2 {α} {β} {γ} u v)
all-scn-S2 u p v q w r with p w r | q w r
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

all-scn-S1 : ∀ {α β γ} u (p : SCN u) → SCN (S1 {α} {β} {γ} u)
all-scn-S1 u p v q =
  S2 u v , S1⇓ , ≈refl , all-scn-S2 u p v q

all-scn-S0 : ∀ {α β γ} → SCN (S0 {α} {β} {γ})
all-scn-S0 u p =
  S1 u , S0⇓ , ≈refl , all-scn-S1 u p

all-scn-Pr2 : ∀ {α β} u (p : SCN u) v (q : SCN v) →
  SCN (Pr2 {α} {β} u v)
all-scn-Pr2 u p v q =
  (u , Fst0⇓ , ≈Fst , p) , (v , Snd0⇓ , ≈Snd , q)

all-scn-Pr1 : ∀ {α β} u (p : SCN u) → SCN (Pr1 {α} {β} u)
all-scn-Pr1 u p v q =
  Pr2 u v , Pr1⇓ , ≈refl , all-scn-Pr2 u p v q

all-scn-Pr0 : ∀ {α β} → SCN (Pr0 {α} {β})
all-scn-Pr0 u p =
  Pr1 u , Pr0⇓ , ≈refl , all-scn-Pr1 u p

all-scn-Fst0 : ∀ {α β} → SCN (Fst0 {α} {β})
all-scn-Fst0 u p = proj₁ p

all-scn-Snd0 : ∀ {α β} → SCN (Snd0 {α} {β})
all-scn-Snd0 u p = proj₂ p

-- ∀ {α} (u : Nf α) → SCN u

all-scn : ∀ {α} (u : Nf α) → SCN u

all-scn K0 =
  all-scn-K0
all-scn (K1 u) =
  all-scn-K1 u (all-scn u)
all-scn S0 =
  all-scn-S0
all-scn (S1 u) =
  all-scn-S1 u (all-scn u)
all-scn (S2 u v) =
  all-scn-S2 u (all-scn u) v (all-scn v)
all-scn Void0 =
  tt
all-scn Pr0 =
  all-scn-Pr0
all-scn (Pr1 u) =
  all-scn-Pr1 u (all-scn u)
all-scn (Pr2 u v) =
  all-scn-Pr2 u (all-scn u) v (all-scn v)
all-scn Fst0 =
  all-scn-Fst0
all-scn Snd0 =
  all-scn-Snd0

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
  K0 , K⇓ , ≈refl , all-scn-K0
all-sc S =
  S0 , S⇓ , ≈refl , all-scn-S0
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
all-sc Void =
  Void0 , Void⇓ , ≈refl , tt
all-sc Pr =
  Pr0 , Pr⇓ , ≈refl , all-scn-Pr0
all-sc Fst =
  Fst0 , Fst⇓ , ≈refl , all-scn-Fst0
all-sc Snd =
  Snd0 , Snd⇓ , ≈refl , all-scn-Snd0
