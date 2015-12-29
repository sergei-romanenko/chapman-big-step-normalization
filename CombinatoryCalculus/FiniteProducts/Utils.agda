module FiniteProducts.Utils where

open import Relation.Binary.PropositionalEquality public

-- A few mod cons

record True : Set where

data Σ (A : Set) (B : A → Set) : Set where
  sig : (a : A) → (b : B a) → Σ A B

σ₀ : {A : Set}{B : A → Set} → (Σ A B) → A
σ₀ (sig x _) = x

σ₁ : {A : Set}{B : A → Set} → (s : Σ A B) → B (σ₀ s)
σ₁ (sig _ y) = y

data _∧_ (A B : Set) : Set where
  pr : (a : A)(b : B) → A ∧ B

pfst : ∀ {A}{B} → A ∧ B → A
pfst (pr a _) = a

psnd : ∀ {A}{B} → A ∧ B → B
psnd (pr _ b) = b

data _∧_∧_ (A B C : Set) : Set where
  tr : (a : A)(b : B)(c : C) → A ∧ B ∧ C

π₀ : ∀ {A}{B}{C} → A ∧ B ∧ C → A
π₀ (tr a _ _) = a

π₁ : ∀ {A}{B}{C} → A ∧ B ∧ C → B
π₁ (tr _ b _) = b

π₂ : ∀ {A}{B}{C} → A ∧ B ∧ C → C
π₂ (tr _ _ c) = c
