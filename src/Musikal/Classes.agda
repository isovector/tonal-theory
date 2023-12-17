module Musikal.Classes where

open import Relation.Binary
open import Agda.Primitive

record Ord (A : Set) : Set₁ where
  field
    _≤_  : Rel A lzero
    _≤?_ : Decidable _≤_

ord≤ : {A : Set} → ⦃ Ord A ⦄ → Rel A lzero
ord≤ ⦃ ord ⦄ = ord .Ord._≤_

ord≤? : {A : Set} → ⦃ ord : Ord A ⦄ → Decidable (ord .Ord._≤_)
ord≤? ⦃ ord ⦄ = ord .Ord._≤?_

