module FiniteProducts.Utils where

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_]) public

data Σ (A : Set) (B : A → Set) : Set where
  sig : (a : A) → B a → Σ A B

σ₁ : {A : Set} → {B : A → Set} → Σ A B → A
σ₁ (sig a _) = a 

σ₂ : {A : Set} → {B : A → Set} → (s : Σ A B) → B (σ₁ s)
σ₂ (sig _ b) = b

data _∧_ (A B : Set) : Set where
  pr : A → B → A ∧ B

π₁ : {A B : Set} → A ∧ B → A
π₁ (pr a _) = a

π₂ : {A B : Set} → A ∧ B → B
π₂ (pr _ b) = b


data _∧_∧_ (A B C : Set) : Set where
  tr : A → B → C → A ∧ B ∧ C

t1 : {A B C : Set} → A ∧ B ∧ C → A
t1 (tr a _ _) = a
t2 : {A B C : Set} → A ∧ B ∧ C → B
t2 (tr _ b _) = b
t3 : {A B C : Set} → A ∧ B ∧ C → C
t3 (tr _ _ c) = c

data True : Set where
  void : True
