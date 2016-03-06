module FullSystem.Structural where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.BigStep
open import FullSystem.StrongComp

--
-- Structurally recursive normalizer.
--

nf : ∀ {α} (x : Tm α) → Nf α

nf x with all-sc x
... | u , p , x⇓u with eval x x⇓u
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
⟨∙⟩⇓-complete C0⇓ = ≈refl
⟨∙⟩⇓-complete C1⇓ = ≈refl
⟨∙⟩⇓-complete (C2l⇓ ⇓w) =
  ≈trans ≈Cl (⟨∙⟩⇓-complete ⇓w)
⟨∙⟩⇓-complete (C2r⇓ ⇓w) =
  ≈trans ≈Cr (⟨∙⟩⇓-complete ⇓w)
⟨∙⟩⇓-complete Inl0⇓ = ≈refl
⟨∙⟩⇓-complete Inr0⇓ = ≈refl
⟨∙⟩⇓-complete Suc0⇓ = ≈refl
⟨∙⟩⇓-complete R0⇓ = ≈refl
⟨∙⟩⇓-complete R1⇓ = ≈refl
⟨∙⟩⇓-complete R2z⇓ = ≈Rz
⟨∙⟩⇓-complete (R2s⇓ {α} {u} {v} {w} {w′} {w′′} {w′′′} ⇓w′ ⇓w′′ ⇓w′′′) = begin
    R ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ (Suc ∙ ⌜ w ⌝)
      ≈⟨ ≈Rs ⟩
    (⌜ v ⌝ ∙ ⌜ w ⌝) ∙ (R ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝)
      ≈⟨ ≈cong∙ (⟨∙⟩⇓-complete ⇓w′) (⟨∙⟩⇓-complete ⇓w′′) ⟩
    ⌜ w′ ⌝ ∙ ⌜ w′′ ⌝
      ≈⟨ ⟨∙⟩⇓-complete ⇓w′′′ ⟩
    ⌜ w′′′ ⌝
    ∎
  where open ≈-Reasoning

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
⇓-complete NE⇓ = ≈refl
⇓-complete Inl⇓ = ≈refl
⇓-complete Inr⇓ = ≈refl
⇓-complete C⇓ = ≈refl
⇓-complete Zero⇓ = ≈refl
⇓-complete Suc⇓ = ≈refl
⇓-complete R⇓ = ≈refl

-- x ≈ ⌜ nf x ⌝

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝

complete x with all-sc x
... | u , p , x⇓u with eval x x⇓u
... | ._ , refl =
  ⇓-complete x⇓u

--
-- Soundness: normalization takes convertible terms to identical normal forms.
--

-- x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound : ∀ {α} {x y : Tm α} {u v : Nf α} →
  x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-sound ≈refl x⇓u x⇓v =
  ⇓-det x⇓u x⇓v
⇓-sound (≈sym x≈y) x⇓u x⇓v =
  sym $ ⇓-sound x≈y x⇓v x⇓u
⇓-sound (≈trans {α} {x} {z} {y} x≈z z≈y) x⇓u y⇓v =
  let w , r , z⇓w = all-sc z
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
⇓-sound ≈Cl (A⇓ (A⇓ (A⇓ C⇓ x⇓ C0⇓) y⇓ C1⇓)
                    (A⇓ Inl⇓ z⇓ Inl0⇓) (C2l⇓ ⇓u)) ⇓v =
  ⇓-det (A⇓ x⇓ z⇓ ⇓u) ⇓v
⇓-sound ≈Cr (A⇓ (A⇓ (A⇓ C⇓ x⇓ C0⇓) y⇓ C1⇓)
                    (A⇓ Inr⇓ z⇓ Inr0⇓) (C2r⇓ ⇓u)) ⇓v =
  ⇓-det (A⇓ y⇓ z⇓ ⇓u) ⇓v
⇓-sound ≈Rz (A⇓ (A⇓ (A⇓ R⇓ ⇓u R0⇓) ⇓w R1⇓) Zero⇓ R2z⇓) ⇓v =
  ⇓-det ⇓u ⇓v
⇓-sound ≈Rs (A⇓ (A⇓ (A⇓ R⇓ p1 R0⇓) p2 R1⇓) (A⇓ Suc⇓ p3 Suc0⇓)
        (R2s⇓ p5 p4 p6))
        (A⇓ (A⇓ q7 q8 q5) (A⇓ (A⇓ (A⇓ R⇓ q1 R0⇓) q2 R1⇓) q3 q4) q6)
  rewrite ⇓-det p1 q1 | ⇓-det p2 q2 | ⇓-det p3 q3 | ⟨∙⟩⇓-det p4 q4 |
          ⇓-det q2 q7 | ⇓-det q3 q8 | ⟨∙⟩⇓-det p5 q5 | ⟨∙⟩⇓-det p6 q6
  = refl

-- x ≈ y → nf x ≡ nf y

sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

sound {α} {x} {y} x≈y with all-sc x | all-sc y
... | u , p , ⇓u | v , q , ⇓v
  with eval x ⇓u | eval y ⇓v
... | ._ , refl | ._ , refl
  = ⇓-sound x≈y ⇓u ⇓v
