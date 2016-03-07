module BasicSystem.Examples where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep
open import BasicSystem.StrongComp
open import BasicSystem.Structural


--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (⋆ ⇒ ⋆)
III = I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆})

--
-- Convertibility.
--

III≈I : III ≈ I
III≈I = begin
  S ∙ K ∙ K ∙ (S ∙ K ∙ K ∙ (S ∙ K ∙ K))
    ≈⟨ ≈cong∙ ≈refl ≈S ⟩
  (S ∙ K ∙ K) ∙ (K ∙ (S ∙ K ∙ K) ∙ (K ∙ (S ∙ K ∙ K)))
    ≈⟨ ≈cong∙ ≈refl ≈K ⟩
  (S ∙ K ∙ K) ∙ (S ∙ K ∙ K)
    ≈⟨ ≈S ⟩
  K ∙ (S ∙ K ∙ K) ∙ (K ∙ (S ∙ K ∙ K))
    ≈⟨ ≈K ⟩
  S ∙ K ∙ K
  ∎
  where open ≈-Reasoning

III≈I′ : III ≈ I
III≈I′ = begin
  (S ∙ K ∙ K) ∙ ((S ∙ K ∙ K) ∙ (S ∙ K ∙ K))
    ≈⟨ ≈S ⟩
  (K ∙ (S ∙ K ∙ K ∙ (S ∙ K ∙ K))) ∙ (K ∙ (S ∙ K ∙ K ∙ (S ∙ K ∙ K)))
    ≈⟨ ≈K ⟩
  (S ∙ K ∙ K) ∙ (S ∙ K ∙ K)
    ≈⟨ ≈S ⟩
  (K ∙ (S ∙ K ∙ K)) ∙ (K ∙ (S ∙ K ∙ K))
    ≈⟨ ≈K ⟩
  S ∙ K ∙ K
  ∎
  where open ≈-Reasoning

--
-- Big-step relational semantics
--

III⇓ : III ⇓ S2 K0 K0
III⇓ = A⇓
  (A⇓ (A⇓ S⇓ K⇓ S0⇓) K⇓ S1⇓)
  (A⇓
    (A⇓ (A⇓ S⇓ K⇓ S0⇓) K⇓ S1⇓)
    (A⇓ (A⇓ S⇓ K⇓ S0⇓) K⇓ S1⇓)
    (S2⇓ K0⇓ K0⇓ K1⇓))
  (S2⇓ K0⇓ K0⇓ K1⇓)

--
-- Structurally recursive normalizer.
--

eval-III : eval III III⇓ ≡ (S2 K0 K0 , refl)
eval-III = refl

--
-- Total (terminating) normalization.
--

all-sc-III : all-sc III ≡
  S2 K0 K0 ,
  (λ w r → w , r , S2⇓ K0⇓ K0⇓ K1⇓) ,
  A⇓
    (A⇓ (A⇓ S⇓ K⇓ S0⇓) K⇓ S1⇓)
    (A⇓
      (A⇓ (A⇓ S⇓ K⇓ S0⇓) K⇓ S1⇓)
      (A⇓ (A⇓ S⇓ K⇓ S0⇓) K⇓ S1⇓)
      (S2⇓ K0⇓ K0⇓ K1⇓))
    (S2⇓ K0⇓ K0⇓ K1⇓)
all-sc-III = refl

nf-III : nf III ≡ S2 K0 K0
nf-III = refl

norm-III : ⌜ nf III ⌝ ≡ S ∙ K ∙ K
norm-III = refl

--
-- Completeness: III ≈ ⌜ nf III ⌝
--

complete-III : III ≈ ⌜ nf III ⌝
complete-III = complete III

complete-III≡ : complete III ≡
  ≈trans (≈cong∙ (≈trans (≈cong∙ (≈trans (≈cong∙ ≈refl ≈refl)
  (≈trans ≈refl ≈refl)) ≈refl) (≈trans ≈refl ≈refl))
  (≈trans (≈cong∙ (≈trans (≈cong∙ (≈trans (≈cong∙ ≈refl ≈refl)
  (≈trans ≈refl ≈refl)) ≈refl)
  (≈trans ≈refl ≈refl))
  (≈trans (≈cong∙ (≈trans (≈cong∙ ≈refl ≈refl)
  (≈trans ≈refl ≈refl)) ≈refl) (≈trans ≈refl ≈refl)))
  (≈trans (≈trans ≈S (≈trans (≈cong∙ ≈refl ≈refl)
          (≈trans ≈K ≈refl))) ≈refl)))
  (≈trans (≈trans ≈S (≈trans (≈cong∙ ≈refl ≈refl)
          (≈trans ≈K ≈refl))) ≈refl)
complete-III≡ = refl
