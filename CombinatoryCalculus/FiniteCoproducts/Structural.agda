module FiniteCoproducts.Structural where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.BigStep
open import FiniteCoproducts.StrongComp

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
⟨∙⟩⇓-complete C0⇓ = ≈refl
⟨∙⟩⇓-complete C1⇓ = ≈refl
⟨∙⟩⇓-complete (C2l⇓ ⇓w) =
  ≈trans ≈Cl (⟨∙⟩⇓-complete ⇓w)
⟨∙⟩⇓-complete (C2r⇓ ⇓w) =
  ≈trans ≈Cr (⟨∙⟩⇓-complete ⇓w)
⟨∙⟩⇓-complete Inl0⇓ = ≈refl
⟨∙⟩⇓-complete Inr0⇓ = ≈refl

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
⇓-complete NE⇓ = ≈refl
⇓-complete Inl⇓ = ≈refl
⇓-complete Inr⇓ = ≈refl
⇓-complete C⇓ = ≈refl

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
⇓-sound ≈Cl (A⇓ (A⇓ (A⇓ C⇓ x⇓ C0⇓) y⇓ C1⇓)
                    (A⇓ Inl⇓ z⇓ Inl0⇓) (C2l⇓ ⇓u)) ⇓v =
  ⇓-det (A⇓ x⇓ z⇓ ⇓u) ⇓v
⇓-sound ≈Cr (A⇓ (A⇓ (A⇓ C⇓ x⇓ C0⇓) y⇓ C1⇓)
                    (A⇓ Inr⇓ z⇓ Inr0⇓) (C2r⇓ ⇓u)) ⇓v =
  ⇓-det (A⇓ y⇓ z⇓ ⇓u) ⇓v

-- x ≈ y → nf x ≡ nf y

sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

sound {α} {x} {y} x≈y with all-sc x | all-sc y
... | u , p , ⇓u , _ | v , q , ⇓v , _
  with eval x ⇓u | eval y ⇓v
... | ._ , refl | ._ , refl
  = ⇓-sound x≈y ⇓u ⇓v
