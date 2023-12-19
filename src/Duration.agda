module Duration where

open import Data.Rational as Rat using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Properties as Rat
open import Data.Integer using (+≤+; +_; +[1+_]; -[1+_])
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality


record 𝔻 : Set where
  constructor mkDur
  field
    duration : ℚ
    positive : 0ℚ Rat.≤ duration

infix 4 _≤_ _<_

_≤_ : 𝔻 → 𝔻 → Set
x ≤ y = 𝔻.duration x Rat.≤ 𝔻.duration y

_<_ : 𝔻 → 𝔻 → Set
x < y = 𝔻.duration x Rat.< 𝔻.duration y

open import Data.Unit using (tt)

infixr 5 _+_
_+_ : 𝔻 → 𝔻 → 𝔻
mkDur d₁ p₁ + mkDur d₂ p₂ = mkDur (d₁ Rat.+ d₂) (Rat.+-mono-≤ p₁ p₂)

infixr 6 _⊔_ _⊓_ _*_

_⊔_ : 𝔻 → 𝔻 → 𝔻
mkDur d₁ p₁ ⊔ mkDur d₂ p₂ = mkDur (d₁ Rat.⊔ d₂) (Rat.⊔-mono-≤ p₁ p₂)

_⊓_ : 𝔻 → 𝔻 → 𝔻
mkDur d₁ p₁ ⊓ mkDur d₂ p₂ = mkDur (d₁ Rat.⊓ d₂) (Rat.⊓-mono-≤ p₁ p₂)

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


≤-refl : {x : 𝔻} → x ≤ x
≤-refl = Rat.≤-refl

≤-trans : {x y z : 𝔻} → x ≤ y → y ≤ z → x ≤ z
≤-trans = Rat.≤-trans

0𝔻≤n : {x : 𝔻} → 0𝔻 ≤ x
0𝔻≤n {mkDur duration positive} = positive

sub : (x y : 𝔻) → y ≤ x → 𝔻
sub (mkDur x px) (mkDur y py) y≤x = mkDur (x Rat.- y)
  ( begin
  0ℚ                 ≡⟨ sym (Rat.+-inverseʳ x) ⟩
  x Rat.+ (Rat.- x)  ≤⟨ Rat.+-monoʳ-≤ x (Rat.neg-antimono-≤ y≤x) ⟩
  x Rat.+ (Rat.- y)  ∎
  )
  where open Rat.≤-Reasoning

+-monoˡ-≤ : (r : 𝔻) → {l₀ l₁ : 𝔻} → l₀ ≤ l₁ → l₀ + r ≤ l₁ + r
+-monoˡ-≤ r l≤l = Rat.+-monoˡ-≤ (𝔻.duration r) l≤l

+-monoʳ-≤ : (r : 𝔻) → {l₀ l₁ : 𝔻} → l₀ ≤ l₁ → r + l₀ ≤ r + l₁
+-monoʳ-≤ r l≤l = Rat.+-monoʳ-≤ (𝔻.duration r) l≤l

sub-mono-≤ : (x y m : 𝔻) → (m≤x : m ≤ x) → (m≤y : m ≤ y) → (x ≤ y) → sub x m m≤x ≤ sub y m m≤y
sub-mono-≤ x y m m≤x m≤y x≤y = Rat.+-monoˡ-≤ (Rat.- 𝔻.duration m) x≤y

x⊓y≤x⊔y : (x y : 𝔻) → x ⊓ y ≤ x ⊔ y
x⊓y≤x⊔y x y = Rat.p⊓q≤p⊔q (𝔻.duration x) (𝔻.duration y)

open import Relation.Nullary

_≟_ : (x y : 𝔻) → Dec (x ≡ y)
x ≟ y with 𝔻.duration x Rat.≟ 𝔻.duration y
(mkDur .duration p ≟ mkDur duration p₁) | yes refl rewrite Rat.≤-irrelevant p p₁ = yes refl
... | no z = no λ { x₁ → z (cong 𝔻.duration x₁) }

_≤?_ : (x y : 𝔻) → Dec (x ≤ y)
x ≤? y = 𝔻.duration x Rat.≤? 𝔻.duration y

<⇒≤ : (x y : 𝔻) → x < y → x ≤ y
<⇒≤ _ _ = Rat.<⇒≤

open import Relation.Binary.Definitions using (Trichotomous; tri<; tri≈; tri>) public

postulate
  <-cmp : Trichotomous _≡_ _<_
-- <-cmp x y with Rat.<-cmp (𝔻.duration x) (𝔻.duration y)
-- ... | tri< a ¬b ¬c = tri< {! !} ? ?
-- ... | tri≈ ¬a b ¬c = tri≈ {! !} ? ?
-- ... | tri> ¬a ¬b c = tri> {! !} ? ?


module ≤-Reasoning where
  open Rat.≤-Reasoning public


2𝔻 = 1𝔻 + 1𝔻
3𝔻 = 2𝔻 + 1𝔻
4𝔻 = 3𝔻 + 1𝔻

