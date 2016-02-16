module NaturalNumbers.Utils where

open import Data.Unit public
  using (⊤; tt)
open import Data.Product as Prod public
  using (_,_; proj₁; proj₂; _×_; Σ; ∃; ∃₂)

open import Function public

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_]) public

open import Relation.Binary public
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
        x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl
