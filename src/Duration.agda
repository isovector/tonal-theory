module Duration where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Agda.Primitive
open import Data.Product


data Duration : Set where
  𝅝． 𝅝 𝅗𝅥． 𝅗𝅥 𝅘𝅥． 𝅘𝅥 𝅘𝅥𝅮． 𝅘𝅥𝅮 𝅘𝅥𝅯． 𝅘𝅥𝅯 𝅘𝅥𝅰． 𝅘𝅥𝅰 ⊘ : Duration
  _⁀_ : Duration → Duration → Duration

infixl 5 _⁀_

durationLength : Duration → ℕ
durationLength 𝅝． = 96
durationLength 𝅝   = 64
durationLength 𝅗𝅥． = 48
durationLength 𝅗𝅥   = 32
durationLength 𝅘𝅥． = 24
durationLength 𝅘𝅥   = 16
durationLength 𝅘𝅥𝅮． = 12
durationLength 𝅘𝅥𝅮   = 8
durationLength 𝅘𝅥𝅯． = 6
durationLength 𝅘𝅥𝅯   = 4
durationLength 𝅘𝅥𝅰． = 3
durationLength 𝅘𝅥𝅰   = 2
durationLength ⊘   = 0
durationLength (x ⁀ y) = durationLength x + durationLength y

_≈ᵈ_ : Rel Duration lzero
x ≈ᵈ y = durationLength x ≡ durationLength y

infix 4 _≈ᵈ_

_+ᵈ_ : Duration → Duration → Duration
⊘   +ᵈ y = y
x   +ᵈ y = x ⁀ y

_measures : ℕ → Duration
zero measures = ⊘
suc x measures = x measures +ᵈ 𝅝

_*ᵈ_ : Duration → ℕ → Duration
d *ᵈ zero = ⊘
d *ᵈ suc y = d *ᵈ y +ᵈ d

infixl 5 _+ᵈ_
infixl 6 _*ᵈ_

