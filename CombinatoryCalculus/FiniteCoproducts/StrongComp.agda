module FiniteCoproducts.StrongComp where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.BigStep

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set

SCN {⋆} u = ⊤
SCN {α ⇒ β} u = ∀ v → SCN v →
  ∃ λ w → SCN w × (u ⟨∙⟩ v ⇓ w) × (⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝)
SCN {Z} u = ⊥
SCN {α + β} (Inl1 u) = SCN u
SCN {α + β} (Inr1 u) = SCN u

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u

all-scn-K1 : ∀ {α β} u (p : SCN u) → SCN (K1 {α} {β} u)
all-scn-K1 u p v q =
  u , p , K1⇓ , ≈K

all-scn-K0 : ∀ {α β} → SCN (K0 {α} {β})
all-scn-K0 u p =
  K1 u , all-scn-K1 u p , K0⇓ , ≈refl

all-scn-S2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  SCN (S2 {α} {β} {γ} u v)
all-scn-S2 u p v q w r with p w r | q w r
... | w₁ , r₁ , ⇓w₁ , ≈w₁ | w₂ , r₂ , ⇓w₂ , ≈w₂ with r₁ w₂ r₂
... | w₃ , r₃ , ⇓w₃ , ≈w₃ =
  w₃ , r₃ , S2⇓ ⇓w₁ ⇓w₂ ⇓w₃ , ≈⌜w₃⌝
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
  S2 u v , all-scn-S2 u p v q , S1⇓ , ≈refl

all-scn-S0 : ∀ {α β γ} → SCN (S0 {α} {β} {γ})
all-scn-S0 u p =
  S1 u , all-scn-S1 u p , S0⇓ , ≈refl

all-scn-Inl0 : ∀ {α β} → SCN (Inl0 {α} {β})
all-scn-Inl0 u p =
  Inl1 u , p , Inl0⇓ , ≈refl

all-scn-Inr0 : ∀ {α β} → SCN (Inr0 {α} {β})
all-scn-Inr0 u p =
  Inr1 u , p , Inr0⇓ , ≈refl

all-scn-C2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  SCN (C2 {α} {β} {γ} u v)
all-scn-C2 u p v q (Inl1 w) r with p w r
... | w′ , r′ , ⇓w′ , ∙≈⌜w′⌝ = w′ , r′ , C2l⇓ ⇓w′ , C≈⌜w′⌝
  where
  open ≈-Reasoning
  C≈⌜w′⌝ : C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inl ∙ ⌜ w ⌝) ≈ ⌜ w′ ⌝
  C≈⌜w′⌝ = begin
    C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inl ∙ ⌜ w ⌝)
      ≈⟨ ≈Cl ⟩
    ⌜ u ⌝ ∙ ⌜ w ⌝
      ≈⟨ ∙≈⌜w′⌝ ⟩
    ⌜ w′ ⌝
    ∎
all-scn-C2 u p v q (Inr1 w) r with q w r
... | w′ , r′ , ⇓w′ , ∙≈⌜w′⌝ = w′ , r′ , C2r⇓ ⇓w′ , C≈⌜w′⌝
  where
  open ≈-Reasoning
  C≈⌜w′⌝ : C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inr ∙ ⌜ w ⌝) ≈ ⌜ w′ ⌝
  C≈⌜w′⌝ = begin
    C ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Inr ∙ ⌜ w ⌝)
      ≈⟨ ≈Cr ⟩
    ⌜ v ⌝ ∙ ⌜ w ⌝
      ≈⟨ ∙≈⌜w′⌝ ⟩
    ⌜ w′ ⌝
    ∎

all-scn-C1 : ∀ {α β γ} u (p : SCN u) → SCN (C1 {α} {β} {γ} u)
all-scn-C1 u p v q =
  C2 u v , all-scn-C2 u p v q , C1⇓ , ≈refl

all-scn-C0 : ∀ {α β γ} → SCN (C0 {α} {β} {γ})
all-scn-C0 u p =
  C1 u , all-scn-C1 u p , C0⇓ , ≈refl

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
all-scn NE0 u =
  λ ()
all-scn Inl0 u =
  all-scn-Inl0 u
all-scn (Inl1 u) =
  all-scn u
all-scn Inr0 u =
  all-scn-Inr0 u
all-scn (Inr1 u) =
  all-scn u
all-scn C0 u =
  all-scn-C0 u
all-scn (C1 u) v =
  all-scn-C1 u (all-scn u) v
all-scn (C2 u v) w =
  all-scn-C2 u (all-scn u) v (all-scn v) w

--
-- "Strong computability" on terms.
--

SC : ∀ {α} (x : Tm α) → Set
SC x = ∃ λ u → SCN u × (x ⇓ u) × (x ≈ ⌜ u ⌝)

--
-- All terms are strongly computable!
--    ∀ {α} (x : Tm α) → SC u
--

all-sc : ∀ {α} (x : Tm α) → SC x

all-sc K =
  K0 , all-scn-K0 , K⇓ , ≈refl
all-sc S =
  S0 , all-scn-S0 , S⇓ , ≈refl
all-sc (x ∙ y) with all-sc x | all-sc y
... | u , p , ⇓u , ≈⌜u⌝ | v , q , ⇓v , ≈⌜v⌝ with p v q
... | w , r , ⇓w , ≈⌜w⌝ =
  w , r , A⇓ ⇓u ⇓v ⇓w , x∙y≈⌜w⌝
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
  NE0 , (λ u → λ ()) , NE⇓ , ≈refl
all-sc Inl =
  Inl0 , all-scn-Inl0 , Inl⇓ , ≈refl
all-sc Inr =
  Inr0 , all-scn-Inr0 , Inr⇓ , ≈refl
all-sc C =
  C0 , all-scn-C0 , C⇓ , ≈refl
