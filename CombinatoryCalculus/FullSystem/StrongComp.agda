module FullSystem.StrongComp where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.BigStep

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set

SCN {⋆} u = ⊤
SCN {α ⇒ β} u = ∀ v → SCN v →
  ∃ λ w → SCN w × (u ⟨∙⟩ v ⇓ w)
SCN {U} u = ⊤
SCN {α * β} u =
  (∃ λ w →  SCN w × (Fst0 ⟨∙⟩ u ⇓ w))
  ×
  (∃ λ w →  SCN w × (Snd0 ⟨∙⟩ u ⇓ w))
SCN {Z} u = ⊥
SCN {α + β} (Inl1 u) = SCN u
SCN {α + β} (Inr1 u) = SCN u
SCN {N} u = ⊤

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u
--

all-scn-K1 : ∀ {α β} u (p : SCN u) → SCN (K1 {α} {β} u)
all-scn-K1 u p v q =
  u , p , K1⇓

all-scn-K0 : ∀ {α β} → SCN (K0 {α} {β})
all-scn-K0 u p =
  K1 u , all-scn-K1 u p , K0⇓

all-scn-S2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  SCN (S2 {α} {β} {γ} u v)
all-scn-S2 u p v q w r with p w r | q w r
... | w₁ , r₁ , ⇓w₁ | w₂ , r₂ , ⇓w₂ with r₁ w₂ r₂
... | w₃ , r₃ , ⇓w₃ =
  w₃ , r₃ , S2⇓ ⇓w₁ ⇓w₂ ⇓w₃

all-scn-S1 : ∀ {α β γ} u (p : SCN u) → SCN (S1 {α} {β} {γ} u)
all-scn-S1 u p v q =
  S2 u v , all-scn-S2 u p v q , S1⇓

all-scn-S0 : ∀ {α β γ} → SCN (S0 {α} {β} {γ})
all-scn-S0 u p =
  S1 u , all-scn-S1 u p , S0⇓

all-scn-Pr2 : ∀ {α β} u (p : SCN u) v (q : SCN v) →
  SCN (Pr2 {α} {β} u v)
all-scn-Pr2 u p v q =
  (u , p , Fst0⇓) , (v , q , Snd0⇓)

all-scn-Pr1 : ∀ {α β} u (p : SCN u) → SCN (Pr1 {α} {β} u)
all-scn-Pr1 u p v q =
  Pr2 u v , all-scn-Pr2 u p v q , Pr1⇓

all-scn-Pr0 : ∀ {α β} → SCN (Pr0 {α} {β})
all-scn-Pr0 u p =
  Pr1 u , all-scn-Pr1 u p , Pr0⇓

all-scn-Fst0 : ∀ {α β} → SCN (Fst0 {α} {β})
all-scn-Fst0 u p = proj₁ p

all-scn-Snd0 : ∀ {α β} → SCN (Snd0 {α} {β})
all-scn-Snd0 u p = proj₂ p

all-scn-Inl0 : ∀ {α β} → SCN (Inl0 {α} {β})
all-scn-Inl0 u p =
  Inl1 u , p , Inl0⇓

all-scn-Inr0 : ∀ {α β} → SCN (Inr0 {α} {β})
all-scn-Inr0 u p =
  Inr1 u , p , Inr0⇓

all-scn-C2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  SCN (C2 {α} {β} {γ} u v)
all-scn-C2 u p v q (Inl1 w) r with p w r
... | w′ , r′ , ⇓w′ = w′ , r′ , C2l⇓ ⇓w′
all-scn-C2 u p v q (Inr1 w) r with q w r
... | w′ , r′ , ⇓w′ = w′ , r′ , C2r⇓ ⇓w′

all-scn-C1 : ∀ {α β γ} u (p : SCN u) → SCN (C1 {α} {β} {γ} u)
all-scn-C1 u p v q =
  C2 u v , all-scn-C2 u p v q , C1⇓

all-scn-C0 : ∀ {α β γ} → SCN (C0 {α} {β} {γ})
all-scn-C0 u p =
  C1 u , all-scn-C1 u p , C0⇓

all-scn-Suc0 : SCN Suc0
all-scn-Suc0 u tt =
  Suc1 u , tt , Suc0⇓

all-scn-R2 : ∀ {α} u (p : SCN {α} u) v (q : SCN v) →
  SCN (R2 u v)
all-scn-R2 u p v q Zero0 tt =
  u , p , R2z⇓
all-scn-R2 {α} u p v q (Suc1 w) tt
  with q w tt | all-scn-R2 u p v q w tt
... | w′ , r′ , ⇓w′ | w′′ , r′′ , ⇓w′′
  with r′ w′′ r′′
... | w′′′ , r′′′ , ⇓w′′′
  = w′′′ , r′′′ , R2s⇓ ⇓w′ ⇓w′′ ⇓w′′′

all-scn-R1 : ∀ {α} u (p : SCN {α} u) →
  SCN (R1 u)
all-scn-R1 u p v q =
  R2 u v , all-scn-R2 u p v q , R1⇓

all-scn-R0 : ∀ {α} →
  SCN (R0 {α})
all-scn-R0 u p =
  R1 u , all-scn-R1 u p , R0⇓

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
all-scn Zero0 =
  tt
all-scn Suc0 =
  all-scn-Suc0
all-scn (Suc1 u) =
  tt
all-scn R0 =
  all-scn-R0
all-scn (R1 u) =
  all-scn-R1 u (all-scn u)
all-scn (R2 u v) =
  all-scn-R2 u (all-scn u) v (all-scn v)

--
-- "Strong computability" on terms.
--

SC : ∀ {α} (x : Tm α) → Set
SC x = ∃ λ u → SCN u × (x ⇓ u)

--
-- All terms are strongly computable!
--    ∀ {α} (x : Tm α) → SC u
--

all-sc : ∀ {α} (x : Tm α) → SC x

all-sc K =
  K0 , all-scn-K0 , K⇓
all-sc S =
  S0 , all-scn-S0 , S⇓
all-sc (x ∙ y) with all-sc x | all-sc y
... | u , p , ⇓u | v , q , ⇓v with p v q
... | w , r , ⇓w =
  w , r , A⇓ ⇓u ⇓v ⇓w
all-sc Void =
  Void0 , tt , Void⇓
all-sc Pr =
  Pr0 , all-scn-Pr0 , Pr⇓
all-sc Fst =
  Fst0 , all-scn-Fst0 , Fst⇓
all-sc Snd =
  Snd0 , all-scn-Snd0 , Snd⇓
all-sc NE =
  NE0 , (λ u → λ ()) , NE⇓
all-sc Inl =
  Inl0 , all-scn-Inl0 , Inl⇓
all-sc Inr =
  Inr0 , all-scn-Inr0 , Inr⇓
all-sc C =
  C0 , all-scn-C0 , C⇓
all-sc Zero =
  Zero0 , tt , Zero⇓
all-sc Suc =
  Suc0 , all-scn-Suc0 , Suc⇓
all-sc R =
  R0 , all-scn-R0 , R⇓
