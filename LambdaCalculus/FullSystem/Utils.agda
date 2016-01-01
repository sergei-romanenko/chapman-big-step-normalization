module FullSystem.Utils where

open import Function using (_∘_) public
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_]) public
open import Data.Product hiding (<_,_>) public

t1 : ∀ {A B C : Set} → A × B × C → A
t1 = proj₁

t2 : ∀ {A B C : Set} → A × B × C → B
t2 = proj₁ ∘ proj₂

t3 : ∀ {A B C : Set} → A × B × C → C
t3 = proj₂ ∘ proj₂

data True : Set where
  void : True

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y z u v w} →
        x ≡ u → y ≡ v → z ≡ w  → f x y z ≡ f u v w
cong₃ f refl refl refl = refl
