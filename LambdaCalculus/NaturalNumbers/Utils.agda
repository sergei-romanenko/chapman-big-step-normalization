module NaturalNumbers.Utils where

open import Function public
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_]) public
open import Data.Unit using (⊤; tt) public
open import Data.Product hiding (<_,_>) public

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y z u v w} →
        x ≡ u → y ≡ v → z ≡ w  → f x y z ≡ f u v w
cong₃ f refl refl refl = refl
