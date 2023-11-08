{-# OPTIONS --rewriting --local-confluence-check #-}

module Duration where

open import Agda.Builtin.Equality.Rewrite

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Agda.Primitive
open import Data.Product


Duration : Set
Duration = ℕ


-- data Duration : Set where
--   𝅝． 𝅝 𝅗𝅥． 𝅗𝅥 𝅘𝅥． 𝅘𝅥 𝅘𝅥𝅮． 𝅘𝅥𝅮 𝅘𝅥𝅯． 𝅘𝅥𝅯 𝅘𝅥𝅰． 𝅘𝅥𝅰 ⊘ : Duration
--   _⁀_ : Duration → Duration → Duration

infixl 5 _⁀_

pattern 𝅝．       = 96
pattern 𝅝         = 64
pattern 𝅗𝅥．       = 48
pattern 𝅗𝅥         = 32
pattern 𝅘𝅥．       = 24
pattern 𝅘𝅥         = 16
pattern 𝅘𝅥𝅮．       = 12
pattern 𝅘𝅥𝅮         = 8
pattern 𝅘𝅥𝅯．       = 6
pattern 𝅘𝅥𝅯         = 4
pattern 𝅘𝅥𝅰．       = 3
pattern 𝅘𝅥𝅰         = 2
pattern ⊘         = 0

_⁀_ = _+_

-- pattern (d₁ ⁀ d₂) = pattern d₁ + pattern d₂

_measures : ℕ → Duration
zero measures = ⊘
suc x measures = 𝅝 ⁀ x measures

-- postulate
--   tie-32-32   : 𝅘𝅥𝅰   ⁀ 𝅘𝅥𝅰   ≡ 𝅘𝅥𝅯
--   tie-16-32   : 𝅘𝅥𝅯   ⁀ 𝅘𝅥𝅰   ≡ 𝅘𝅥𝅯．
--   tie-32-16   : 𝅘𝅥𝅰   ⁀ 𝅘𝅥𝅯   ≡ 𝅘𝅥𝅯．
--   tie-16．-32 : 𝅘𝅥𝅯． ⁀ 𝅘𝅥𝅰   ≡ 𝅘𝅥𝅮
--   tie-32-16． : 𝅘𝅥𝅰   ⁀ 𝅘𝅥𝅯． ≡ 𝅘𝅥𝅮
--   tie-16-16   : 𝅘𝅥𝅯   ⁀ 𝅘𝅥𝅯   ≡ 𝅘𝅥𝅮
--   tie-8-16    : 𝅘𝅥𝅮   ⁀ 𝅘𝅥𝅯   ≡ 𝅘𝅥𝅮．
--   tie-16-8    : 𝅘𝅥𝅯   ⁀ 𝅘𝅥𝅮   ≡ 𝅘𝅥𝅮．
--   tie-8．-16  : 𝅘𝅥𝅮． ⁀ 𝅘𝅥𝅯   ≡ 𝅘𝅥
--   tie-16-8．  : 𝅘𝅥𝅯   ⁀ 𝅘𝅥𝅮． ≡ 𝅘𝅥
--   tie-8-8     : 𝅘𝅥𝅮   ⁀ 𝅘𝅥𝅮   ≡ 𝅘𝅥
--   tie-4-8     : 𝅘𝅥   ⁀ 𝅘𝅥𝅮   ≡ 𝅘𝅥．
--   tie-8-4     : 𝅘𝅥𝅮   ⁀ 𝅘𝅥   ≡ 𝅘𝅥．
--   tie-4．-8   : 𝅘𝅥． ⁀ 𝅘𝅥𝅮   ≡ 𝅗𝅥
--   tie-8-4．   : 𝅘𝅥𝅮   ⁀ 𝅘𝅥． ≡ 𝅗𝅥
--   tie-4-4     : 𝅘𝅥   ⁀ 𝅘𝅥   ≡ 𝅗𝅥
--   tie-2-4     : 𝅗𝅥   ⁀ 𝅘𝅥   ≡ 𝅗𝅥．
--   tie-4-2     : 𝅘𝅥   ⁀ 𝅗𝅥   ≡ 𝅗𝅥．
--   tie-2．-4   : 𝅗𝅥． ⁀ 𝅘𝅥   ≡ 𝅝
--   tie-4-2．   : 𝅘𝅥   ⁀ 𝅗𝅥． ≡ 𝅝
--   tie-2-2     : 𝅗𝅥   ⁀ 𝅗𝅥   ≡ 𝅝
--   tie-1-2     : 𝅝   ⁀ 𝅗𝅥   ≡ 𝅝．
--   tie-2-1     : 𝅗𝅥   ⁀ 𝅝   ≡ 𝅝．
--   tie-⊘ˡ       : ∀ d → ⊘ ⁀ d ≡ d
--   tie-⊘ʳ       : ∀ d → d ⁀ ⊘ ≡ d
--   tie-tie     : ∀ d₁ d₂ d₃ → d₁ ⁀ (d₂ ⁀ d₃) ≡ d₁ ⁀ d₂ ⁀ d₃

-- {-# REWRITE +-assoc +-identityʳ
--   tie-32-32
--   tie-16-32
--   tie-32-16
--   tie-16．-32
--   tie-32-16．
--   tie-16-16
--   tie-8-16
--   tie-16-8
--   tie-8．-16
--   tie-16-8．
--   tie-8-8
--   tie-4-8
--   tie-8-4
--   tie-4．-8
--   tie-8-4．
--   tie-4-4
--   tie-2-4
--   tie-4-2
--   tie-2．-4
--   tie-4-2．
--   tie-2-2
--   tie-1-2
--   tie-2-1
--   tie-⊘ˡ
--   tie-⊘ʳ
--      #-}

_+ᵈ_ : Duration → Duration → Duration
x +ᵈ y  = x ⁀ y

_*ᵈ_ : Duration → ℕ → Duration
d *ᵈ zero = ⊘
d *ᵈ suc y = d +ᵈ d *ᵈ y

infixl 5 _+ᵈ_
infixl 6 _*ᵈ_

postulate
  +ᵈ-assoc : ∀ x y z → (x +ᵈ y) +ᵈ z ≡ x +ᵈ (y +ᵈ z)

