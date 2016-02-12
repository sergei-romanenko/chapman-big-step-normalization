module FiniteProducts.Utils where

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
