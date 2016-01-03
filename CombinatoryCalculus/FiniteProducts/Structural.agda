module FiniteProducts.Structural where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep
open import FiniteProducts.StrongComp

nf : ∀ {α} (x : Tm α) → Nf α
nf x with all-sc x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | u′ , u′≡u = u′

complete : ∀ {α} (x : Tm α) → x ≈ ⌜ nf x ⌝
complete x with all-sc x
... | u , x⇓u , scn-u , x≈⌜u⌝ with eval x x⇓u
... | ._ , refl = x≈⌜u⌝
