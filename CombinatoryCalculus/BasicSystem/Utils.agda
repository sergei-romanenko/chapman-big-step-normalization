module BasicSystem.Utils where

open import Function public
open import Relation.Binary.PropositionalEquality public
open import Data.Product public

-- A few mod cons

record True : Set where

data _∧_∧_ (A B C : Set) : Set where
  tr : (a : A)(b : B)(c : C) → A ∧ B ∧ C

π₀ : ∀ {A}{B}{C} → A ∧ B ∧ C → A
π₀ (tr a _ _) = a

π₁ : ∀ {A}{B}{C} → A ∧ B ∧ C → B
π₁ (tr _ b _) = b

π₂ : ∀ {A}{B}{C} → A ∧ B ∧ C → C
π₂ (tr _ _ c) = c

--_∧_∧_ A B C = A × B × C
--π₀ = proj₁
--π₁ = proj₁ ∘ proj₂
--π₂ = proj₁ ∘ proj₂ ∘ proj₂
