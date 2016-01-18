module NaturalNumbers.Structural where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep
open import NaturalNumbers.StrongComp

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

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝

complete x with all-sc x
... | u , p , x⇓u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl = x≈⌜u⌝

--
-- Soundness: normalisation takes convertible terms to identical normal forms.
--

sound : ∀ {α} (x y : Tm α) → x ≈ y → ⌜ nf x ⌝ ≈ ⌜ nf y ⌝

sound x y x≈y with all-sc x | all-sc y
... | u , p , x⇓u , x≈⌜u⌝ | v , q , y⇓v , y≈⌜v⌝
  with eval x x⇓u | eval y y⇓v
... | u′ , u′≡u | v′ , v′≡v = begin
  ⌜ u′ ⌝
    ≡⟨ cong ⌜_⌝ u′≡u ⟩
  ⌜ u ⌝
    ≈⟨ ≈sym x≈⌜u⌝ ⟩
  x
    ≈⟨ x≈y ⟩
  y
    ≈⟨ y≈⌜v⌝ ⟩
  ⌜ v ⌝
    ≡⟨ sym (cong ⌜_⌝ v′≡v) ⟩
  ⌜ v′ ⌝
  ∎
  where
  open ≈-Reasoning
