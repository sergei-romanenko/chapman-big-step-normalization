module FiniteProducts.Structural where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep
open import FiniteProducts.StrongComp

--
-- Structurally recursive normalizer.
--

nf : ∀ {α} (x : Tm α) → Nf α

nf x with all-sc x
... | u , p , x⇓u , x≈⌜u⌝ with eval x x⇓u
... | u′ , u′≡u = u′

--
-- Completeness: terms are convertible to their normal forms.
--

⟨∙⟩⇓-complete : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α} {w : Nf β} →
  u ⟨∙⟩ v ⇓ w → ⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝

⟨∙⟩⇓-complete K0⇓ = ≈refl
⟨∙⟩⇓-complete K1⇓ = ≈K
⟨∙⟩⇓-complete S0⇓ = ≈refl
⟨∙⟩⇓-complete S1⇓ = ≈refl
⟨∙⟩⇓-complete (S2⇓ {u = u} {v} {w} {w′} {w′′} {w′′′} ⇓w′ ⇓w′′ ⇓w′′′) = begin
  S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝
    ≈⟨ ≈S ⟩
  (⌜ u ⌝ ∙ ⌜ w ⌝) ∙ (⌜ v ⌝ ∙ ⌜ w ⌝)
    ≈⟨ ≈cong∙ (⟨∙⟩⇓-complete ⇓w′) (⟨∙⟩⇓-complete ⇓w′′) ⟩
  ⌜ w′ ⌝ ∙ ⌜ w′′ ⌝
    ≈⟨ ⟨∙⟩⇓-complete ⇓w′′′ ⟩
  ⌜ w′′′ ⌝
  ∎
  where open ≈-Reasoning
⟨∙⟩⇓-complete Pr0⇓ = ≈refl
⟨∙⟩⇓-complete Pr1⇓ = ≈refl
⟨∙⟩⇓-complete Fst0⇓ = ≈Fst
⟨∙⟩⇓-complete Snd0⇓ = ≈Snd

-- x ⇓ u → x ≈ ⌜ u ⌝

⇓-complete : ∀ {α} {x : Tm α} {u : Nf α} →
  x ⇓ u → x ≈ ⌜ u ⌝

⇓-complete K⇓ = ≈refl
⇓-complete S⇓ = ≈refl
⇓-complete (A⇓ {x = x} {y} {u} {v} {w} x⇓u y⇓v ⇓w) =
 begin
  x ∙ y
    ≈⟨ ≈cong∙ (⇓-complete x⇓u) (⇓-complete y⇓v) ⟩
  ⌜ u ⌝ ∙ ⌜ v ⌝
    ≈⟨ ⟨∙⟩⇓-complete ⇓w ⟩
  ⌜ w ⌝
  ∎
  where open ≈-Reasoning
⇓-complete Void⇓ = ≈refl
⇓-complete Pr⇓ = ≈refl
⇓-complete Fst⇓ = ≈refl
⇓-complete Snd⇓ = ≈refl

-- x ≈ ⌜ nf x ⌝

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝

complete x with all-sc x
... | u , p , x⇓u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl =
  ⇓-complete x⇓u

--
-- Soundness: normalisation takes convertible terms to identical normal forms.
--

-- x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound : ∀ {α} {x y : Tm α} {u v : Nf α} →
  x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound ≈refl x⇓u x⇓v =
  ⇓-det x⇓u x⇓v
⇓-sound (≈sym x≈y) x⇓u x⇓v =
  sym $ ⇓-sound x≈y x⇓v x⇓u
⇓-sound (≈trans {α} {x} {z} {y} x≈z z≈y) x⇓u y⇓v =
  let w , r , z⇓w , _ = all-sc z
  in trans (⇓-sound x≈z x⇓u z⇓w) (⇓-sound z≈y z⇓w y⇓v)
⇓-sound ≈K (A⇓ (A⇓ K⇓ x⇓′ K0⇓) y⇓ K1⇓) x⇓′′ =
  ⇓-det x⇓′ x⇓′′
⇓-sound ≈S
  (A⇓ (A⇓ (A⇓ S⇓ x⇓ S0⇓) y⇓ S1⇓) z⇓ (S2⇓ ⇓uw ⇓vw ⇓uwvw))
  xzyz⇓ =
  ⇓-det (A⇓ (A⇓ x⇓ z⇓ ⇓uw) (A⇓ y⇓ z⇓ ⇓vw) ⇓uwvw) xzyz⇓
⇓-sound (≈cong∙ x≈x′ y≈y′) (A⇓ ⇓u ⇓v ⇓uv) (A⇓ ⇓u′ ⇓v′ ⇓u′v′)
  rewrite ⇓-sound x≈x′ ⇓u ⇓u′ | ⇓-sound y≈y′ ⇓v ⇓v′  =
  ⟨∙⟩⇓-det ⇓uv ⇓u′v′
⇓-sound ≈Fst (A⇓ Fst⇓ (A⇓ (A⇓ Pr⇓ y⇓u Pr0⇓) ⇓w Pr1⇓) Fst0⇓) y⇓v =
  ⇓-det y⇓u y⇓v
⇓-sound ≈Snd (A⇓ Snd⇓ (A⇓ (A⇓ Pr⇓ x⇓ Pr0⇓) y⇓u Pr1⇓) Snd0⇓) y⇓v =
  ⇓-det y⇓u y⇓v

-- x ≈ y → nf x ≡ nf y

sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

sound {α} {x} {y} x≈y with all-sc x | all-sc y
... | u , p , ⇓u , _ | v , q , ⇓v , _
  with eval x ⇓u | eval y ⇓v
... | ._ , refl | ._ , refl
  = ⇓-sound x≈y ⇓u ⇓v
