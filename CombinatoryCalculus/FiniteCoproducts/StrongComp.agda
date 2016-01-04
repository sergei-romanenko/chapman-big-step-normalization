module FiniteCoproducts.StrongComp where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.BigStep

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set
SCN {⋆} u = ⊤
SCN {α ⇒ β} u =
  ∀ v → SCN v → ∃ λ w → (u ⟨∙⟩ v ⇓ w) × (⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝) × SCN w
SCN {Zero} u = ⊥
SCN {α + β} (Inl1 u) = SCN u
SCN {α + β} (Inr1 u) = SCN u

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u

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


all-scn-Inl1 : ∀ {α β} u (p : SCN u) →
  ∃ λ w → Inl0 {α} {β}  ⟨∙⟩ u ⇓ w × Inl ∙ ⌜ u ⌝ ≈ ⌜ w ⌝ × SCN w
all-scn-Inl1 u p =
  Inl1 u , Inl0⇓ , ≈refl , p

all-scn-Inr1 : ∀ {α β} u (p : SCN u) →
  ∃ λ w → Inr0 {α} {β} ⟨∙⟩ u ⇓ w × Inr ∙ ⌜ u ⌝ ≈ ⌜ w ⌝ × SCN w
all-scn-Inr1 u p =
  Inr1 u , Inr0⇓ , ≈refl , p

all-scn-C3 : ∀ {α β γ} (u : Nf (α ⇒ γ))(p : SCN u) (v : Nf (β ⇒ γ))(q : SCN v) (w : Nf (α + β)) →
   SCN w → 
    ∃ λ w′ → (C2 u v ⟨∙⟩ w ⇓ w′) × (C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝ ≈ ⌜ w′ ⌝) × SCN w′
all-scn-C3 u p v q (Inl1 w) r with p w r
... | w′ , ⇓w′ , ∙≈⌜w′⌝ , r′ = w′ , C2L⇓ ⇓w′ , C≈⌜w′⌝ , r′
  where
  open ≈-Reasoning
  C≈⌜w′⌝ : C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inl ∙ ⌜ w ⌝) ≈ ⌜ w′ ⌝
  C≈⌜w′⌝ = begin
    C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inl ∙ ⌜ w ⌝)
      ≈⟨ Cl ⟩
    ⌜ u ⌝ ∙ ⌜ w ⌝
      ≈⟨ ∙≈⌜w′⌝ ⟩
    ⌜ w′ ⌝
    ∎

all-scn-C3 u p v q (Inr1 w) r with q w r
... | w′ , ⇓w′ , ∙≈⌜w′⌝ , r′ = w′ , C2R⇓ ⇓w′ , C≈⌜w′⌝ , r′
  where
  open ≈-Reasoning
  C≈⌜w′⌝ : C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inr ∙ ⌜ w ⌝) ≈ ⌜ w′ ⌝
  C≈⌜w′⌝ = begin
    C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inr ∙ ⌜ w ⌝)
      ≈⟨ Cr ⟩
    ⌜ v ⌝ ∙ ⌜ w ⌝
      ≈⟨ ∙≈⌜w′⌝ ⟩
    ⌜ w′ ⌝
    ∎

all-scn-C2 : ∀ {α β γ}
  (u : Nf (α ⇒ γ)) (p : SCN u) (v : Nf (β ⇒ γ)) (q : SCN v) →
    ∃ λ w → C1 u ⟨∙⟩ v ⇓ w × ⌜ C1 u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝ × SCN w
all-scn-C2 u p v q =
  C2 u v , C1⇓ , ≈refl , all-scn-C3 u p v q

all-scn-C1 : ∀ {α β γ} (u : Nf (α ⇒ γ)) (p : SCN u) →
  ∃ (λ w → C0 {β = β} ⟨∙⟩ u ⇓ w × ⌜ C0 ⌝ ∙ ⌜ u ⌝ ≈ ⌜ w ⌝ × SCN w)
all-scn-C1 u p =
  C1 u , C0⇓ , ≈refl , all-scn-C2 u p

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
all-scn NE0 u =
  λ ()
all-scn Inl0 u =
  all-scn-Inl1 u
all-scn (Inl1 u) =
  all-scn u
all-scn Inr0 u =
  λ (p : SCN u) → Inr1 u , Inr0⇓ , ≈refl , p
all-scn (Inr1 u) =
  all-scn u
all-scn C0 u =
  all-scn-C1 u
all-scn (C1 u) v =
  all-scn-C2 u (all-scn u) v
all-scn (C2 u v) w =
  all-scn-C3 u (all-scn u) v (all-scn v) w

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
all-sc NE =
  NE0 , NE⇓ , ≈refl , (λ u → λ ())
all-sc Inl =
  Inl0 , Inl⇓ , ≈refl , all-scn-Inl1
all-sc Inr =
  Inr0 , Inr⇓ , ≈refl , all-scn-Inr1
all-sc C =
  C0 , C⇓ , ≈refl , all-scn-C1
