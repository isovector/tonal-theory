module Duration where

open import Data.Rational as Rat using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Properties as Rat
open import Data.Integer hiding (_+_; _*_; _≤_; positive; _⊔_)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality

record 𝔻 : Set where
  constructor mkDur
  field
    duration : ℚ
    positive : 0ℚ Rat.≤ duration

opaque
  open import Data.Unit using (tt)

  infix 4 _≤_
  infixr 5 _+_
  _+_ : 𝔻 → 𝔻 → 𝔻
  mkDur d₁ p₁ + mkDur d₂ p₂ = mkDur (d₁ Rat.+ d₂) (Rat.+-mono-≤ p₁ p₂)

  infixr 6 _⊔_ _*_
  _⊔_ : 𝔻 → 𝔻 → 𝔻
  mkDur d₁ p₁ ⊔ mkDur d₂ p₂ = mkDur (d₁ Rat.⊔ d₂) (Rat.⊔-mono-≤ p₁ p₂)

  _*_ : 𝔻 → 𝔻 → 𝔻
  mkDur d₁ p₁ * mkDur d₂ p₂ = mkDur (d₁ Rat.* d₂) ( begin
    0ℚ Rat.* 0ℚ  ≤⟨ Rat.*-monoʳ-≤-nonNeg 0ℚ tt p₁ ⟩
    d₁ Rat.* 0ℚ  ≤⟨ Rat.*-monoˡ-≤-nonNeg d₁ (Rat.nonNegative p₁) p₂ ⟩
    d₁ Rat.* d₂  ∎)
    where open Rat.≤-Reasoning

  0𝔻 : 𝔻
  0𝔻 = mkDur 0ℚ Rat.≤-refl

  1𝔻 : 𝔻
  1𝔻 = mkDur 1ℚ (Rat._≤_.*≤* (+≤+ z≤n))

  fromℕ : ℕ → 𝔻
  fromℕ zero = 0𝔻
  fromℕ (ℕ.suc x) = 1𝔻 + fromℕ x

  _⁻¹ : 𝔻 → 𝔻
  mkDur (Rat.mkℚ (+ zero) d isCoprime) p ⁻¹ = 0𝔻
  mkDur r@(Rat.mkℚ +[1+ n ] d isCoprime) p ⁻¹ = mkDur (Rat.1/ r) (Rat._≤_.*≤* (+≤+ z≤n))
  mkDur (Rat.mkℚ (-[1+_] n) d isCoprime) (Rat._≤_.*≤* ()) ⁻¹

  postulate
    ⁻¹∘⁻¹ : ∀ m → (m ⁻¹) ⁻¹ ≡ m
  -- ⁻¹∘⁻¹ (mkDur r@(Rat.mkℚ (+_ zero) d isCoprime) positive) = {! !}
  -- ⁻¹∘⁻¹ (mkDur r@(Rat.mkℚ +[1+ n ] d isCoprime) positive) = {! !}
  -- ⁻¹∘⁻¹ (mkDur (Rat.mkℚ (-[1+_] n) d isCoprime) (Rat.*≤* ()))

  _/_ : 𝔻 → 𝔻 → 𝔻
  x / y = x * y ⁻¹

  postulate
    *-identityʳ : ∀ x → x * 1𝔻 ≡ x

  _≤_ : 𝔻 → 𝔻 → Set
  x ≤ y = 𝔻.duration x Rat.≤ 𝔻.duration y

  ≤-refl : {x : 𝔻} → x ≤ x
  ≤-refl = Rat.≤-refl

  0𝔻≤n : {x : 𝔻} → 0𝔻 ≤ x
  0𝔻≤n {mkDur duration positive} = positive


2𝔻 = 1𝔻 + 1𝔻
3𝔻 = 2𝔻 + 1𝔻
4𝔻 = 3𝔻 + 1𝔻

