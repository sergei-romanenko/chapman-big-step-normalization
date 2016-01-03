module FullSystem.Structural where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.BigStep
open import FullSystem.StrongComp

nf : ∀ {α} (x : Tm α) → Nf α
nf x with all-sc x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | u′ , u′≡u = u′

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝
complete x with all-sc x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl = x≈⌜u⌝
