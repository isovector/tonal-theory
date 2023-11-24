module Fenceposts.Duration where

open import Data.Rational
  using (ℚ; 0ℚ; 1ℚ)
  renaming (½ to ½ʳ; 1/_ to 1/ʳ)
  renaming (_<_ to _<ʳ_; _≥_ to _≥ʳ_; _*_ to _*ʳ_; _-_ to _-ʳ_; _÷_ to _÷ʳ_; _/_ to _/ʳ_)

open import Data.Rational.Properties
  using (≤-refl)

open import Data.Rational.Properties
  using (module ≤-Reasoning)

data DurationIndex : Set where
  diDuration diInterval : DurationIndex

private variable
  di : DurationIndex

data RawDuration : DurationIndex → Set where
  dur : (rational : ℚ) → 0ℚ <ʳ rational → RawDuration diDuration
  int : (rational : ℚ) → 0ℚ <ʳ rational → rational <ʳ 1ℚ → RawDuration di

open import Relation.Binary using (Rel)

_≥ᵈ_ : Rel (RawDuration di) _
dur r x    ≥ᵈ dur r₁ x₁ = r ≥ʳ r₁
dur r x    ≥ᵈ int r₁ x₁ x₂ = r ≥ʳ r₁
int r x x₁ ≥ᵈ dur r₁ x₂ = r ≥ʳ r₁
int r x x₁ ≥ᵈ int r₁ x₂ x₃ = r ≥ʳ r₁

≥ᵈ-refl : {d : RawDuration di} → d ≥ᵈ d
≥ᵈ-refl {d = dur r x} = ≤-refl
≥ᵈ-refl {d = int r x x₁} = ≤-refl

open import Data.Nat using (ℕ)
open import Data.Integer using (1ℤ)

Duration : Set
Duration = RawDuration diDuration

Interval : Set
Interval = RawDuration diInterval


postulate
  trust-me : {A : Set} → A

_*ᵈ_ : RawDuration di → RawDuration di → RawDuration di
dur r x *ᵈ dur r₁ x₁ = dur (r *ʳ r₁) trust-me
dur r x *ᵈ int r₁ x₁ x₂ = dur (r *ʳ r₁) trust-me
int r x x₁ *ᵈ dur r₁ x₂ = dur (r *ʳ r₁) trust-me
int r x x₁ *ᵈ int r₁ x₂ x₃ = int (r *ʳ r₁) trust-me trust-me

1/ : RawDuration di → RawDuration di
1/ (dur r x) = dur (1/ʳ r {trust-me}) trust-me
1/ (int r x x₁) = int (1/ʳ r {trust-me}) trust-me trust-me

_⁺ : Interval → Interval
int r₁ 0<₁ ₁<1 ⁺ = int (1ℚ -ʳ r₁) trust-me trust-me

half : RawDuration di → RawDuration di
half (dur rational x) = dur (rational *ʳ (1ℤ /ʳ 2 )) trust-me
half (int rational x x₁) = int (rational *ʳ (1ℤ /ʳ 2 )) trust-me trust-me

𝅝 : Duration
𝅝 = dur 1ℚ (_<ʳ_.*<* (Data.Integer.+<+ (Data.Nat.s≤s Data.Nat.z≤n)))

𝅗𝅥 : RawDuration di
𝅗𝅥 {diDuration} = dur (1ℤ /ʳ 2) (_<ʳ_.*<* (Data.Integer.+<+ (Data.Nat.s≤s Data.Nat.z≤n)))
𝅗𝅥 {diInterval} = int (1ℤ /ʳ 2) (_<ʳ_.*<* (Data.Integer.+<+ (Data.Nat.s≤s Data.Nat.z≤n))) (_<ʳ_.*<* (Data.Integer.+<+ (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))

½ : Interval
½ = 𝅗𝅥

𝅗𝅥． : RawDuration di
𝅗𝅥． {diDuration} = dur (Data.Integer.+ 3 /ʳ 4) (_<ʳ_.*<* (Data.Integer.+<+ (Data.Nat.s≤s Data.Nat.z≤n)))
𝅗𝅥． {diInterval} = int (Data.Integer.+ 3 /ʳ 4) (_<ʳ_.*<* (Data.Integer.+<+ (Data.Nat.s≤s Data.Nat.z≤n))) (_<ʳ_.*<* (Data.Integer.+<+ (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))))

toDuration : RawDuration di → Duration
toDuration (dur rational x) = dur rational x
toDuration (int rational x x₁) = dur rational x

