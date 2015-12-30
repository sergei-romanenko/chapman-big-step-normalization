module FiniteCoproducts.Utils where

open import Function public
open import Relation.Binary.PropositionalEquality public
open import Data.Unit using (⊤) public
open import Data.Empty public
open import Data.Product public

π₀ : ∀ {A B C : Set} → A × B × C → A
π₀ = proj₁

π₁ : ∀ {A B C : Set} → A × B × C → B
π₁ = proj₁ ∘ proj₂

π₂ : ∀ {A B C : Set} → A × B × C → C
π₂ = proj₂ ∘ proj₂
