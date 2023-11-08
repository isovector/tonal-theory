module Duration where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Agda.Primitive
open import Data.Product


abstract
  Duration : Set
  Duration = ℕ

  beat : Duration
  beat = 1

  _+ᵈ_ : Duration → Duration → Duration
  _+ᵈ_ = _+_

  _*ᵈ_ : Duration → ℕ → Duration
  _*ᵈ_ = _*_

  infixl 5 _+ᵈ_
  infixl 6 _*ᵈ_

  +ᵈ-assoc : ∀ x y z → (x +ᵈ y) +ᵈ z ≡ x +ᵈ (y +ᵈ z)
  +ᵈ-assoc = +-assoc

