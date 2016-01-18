module NaturalNumbers.StrongComp where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set

SCN {⋆} u = ⊤
SCN {α ⇒ β} u = ∀ v → SCN v →
  ∃ λ w → SCN w × (u ⟨∙⟩ v ⇓ w)
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
all-sc Zero =
  Zero0 , tt , Zero⇓
all-sc Suc =
  Suc0 , all-scn-Suc0 , Suc⇓
all-sc R =
  R0 , all-scn-R0 , R⇓
