module BasicSystem.Utils where

open import Function using (_∘_) public
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_]) public
open import Data.Product public

t1 : ∀ {A B C : Set} → A × B × C → A
t1 = proj₁

t2 : ∀ {A B C : Set} → A × B × C → B
t2 = proj₁ ∘ proj₂

t3 : ∀ {A B C : Set} → A × B × C → C
t3 = proj₂ ∘ proj₂

data One : Set where
  void : One
