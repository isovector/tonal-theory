{-# OPTIONS --rewriting #-}

module Fenceposts where

open import Agda.Builtin.Equality.Rewrite

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel; Decidable; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Function using (Injective)
open import Data.Product hiding (map)
open import Data.Nat hiding (_⊔_; >-nonZero)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)

iterateN : {A : Set} → ℕ → A → (A → A) → A
iterateN zero    b f = b
iterateN (suc n) b f = f (iterateN n b f)

open import Data.Nat.Properties using (+-assoc)

{-# REWRITE +-assoc #-}


open Data.Nat
  renaming (ℕ to Note; zero to base; suc to step; _≤_ to _≤ⁿ_)
  hiding (_⊔_; >-nonZero)
  public

open import Fenceposts.Duration

open import Data.Integer using (1ℤ)

-- subdivide : ℕ → Interval → Interval
-- subdivide n d = d *ᵈ (1ℤ / suc n)


open import Data.Unit using (⊤; tt)

Consonant : Rel Note lzero
Consonant _ _ = ⊤

open import Data.List
  renaming ([] to fin; _∷_ to _▹_)
  using (List; _++_; _∷ʳ_)
  public

private variable
  n n₁ n₂ n₃ : Note
  t t₁ t₂ t₃ : Interval
  d d₁ d₂ d₃ : Interval

data Direction : Set where
  dir↑ dir↓ : Direction

otherDirection : Direction → Direction
otherDirection dir↑ = dir↓
otherDirection dir↓ = dir↑

private variable
  dir : Direction

infixr 4 _↑_ _↓_

_⇑_ : Note → ℕ → Note
n ⇑ s = n + s

mutual
  data Motion : Direction → ℕ → Rel Note lzero where
    [_]  : Span n₁ n₂ → Motion dir 1 n₁ n₂
    _↑_ : {size : ℕ}
           → Span n₁ (step n₁)
           → Motion dir↑ (suc size) (step n₁) n₂
           → Motion dir↑ (suc (suc size)) n₁ n₂
    _↓_ : {size : ℕ}
           → Span (step n₂) n₂
           → Motion dir↓ (suc size) n₂ n₁
           → Motion dir↓ (suc (suc size)) (step n₂) n₁

  -- spans are motion
  data Span : Rel Note lzero where
    stay : Span n n
    rest : Span n n
    rearticulate : (d : Interval) → d ≥ᵈ ½ → Span n₁ n₁ → Span n₁ n₂ → Span n₁ n₂
    step↑ : Span n (step n)
    step↓ : Span (step n) n
    -- trans : Consonant n₁ n₂ → Consonant n₂ n₃ → Span d n₁ n₂ → Post 1ℚ n₂ → Span d n₂ n₃ → Span d n₁ n₃
    motion↑ : (size : ℕ) → Motion dir↑ size n (n ⇑ size) → Span n (n ⇑ size)
    motion↓ : (size : ℕ) → Motion dir↓ size (n ⇑ size) n → Span (n ⇑ size) n
    neighbor↑ : (d : Interval) → d ≥ᵈ ½ → Span n (step n) → Span (step n) n → Span n n
    neighbor↓ : (d : Interval) → d ≥ᵈ ½ → Span (step n) n → Span n (step n) → Span (step n) (step n)

-- data Section : Rel Note lzero where
--   section : Span n₁ n₂ → (d₂ : Interval) → Section (d₁ +ᵈ d₂) n₁ n₂

open import Data.Rational.Properties
  using (≤-refl)

instance
  inst-≥ = ≤-refl

  inst-≥ᵈ : ∀ {di} {d : RawDuration di} → d ≥ᵈ d
  inst-≥ᵈ = ≥ᵈ-refl

  inst-[] : ⦃ Span n₁ n₂ ⦄ → Motion dir 1 n₁ n₂
  inst-[] ⦃ x ⦄ = [ x ]

  inst-↑<>
    : ∀ {size}
    → ⦃ Span n₁ (step n₁) ⦄
    → ⦃ Motion dir↑ (suc size) (step n₁) n₂ ⦄
    → Motion dir↑ (suc (suc size)) n₁ n₂
  inst-↑<> ⦃ s ⦄ ⦃ m ⦄ = s ↑ m

  inst-↓<>
    : ∀ {size}
    → ⦃ Span (step n₂) n₂ ⦄
    → ⦃ Motion dir↓ (suc size) n₂ n₁ ⦄
    → Motion dir↓ (suc (suc size)) (step n₂) n₁
  inst-↓<> ⦃ s ⦄ ⦃ m ⦄ = s ↓ m

  inst-stay : Span n n
  inst-stay = stay

  inst-step↑ : Span n _
  inst-step↑ = step↑

  inst-step↓ : Span _ n
  inst-step↓ = step↓


Score : Set
Score = List (Maybe Note × Duration)

mutual
  unparse-motion : ∀ {size} → Duration → Motion dir size n₁ n₂ → Score
  unparse-motion d [ s ] = unparse-span d s
  unparse-motion d (s ↑ m) = unparse-span d s ++ unparse-motion d m
  unparse-motion d (s ↓ m) = unparse-span d s ++ unparse-motion d m

  unparse-span : Duration → Span n₁ n₂ → Score
  unparse-span {n} d stay = (just n , toDuration d) ▹ fin
  unparse-span d rest = (nothing , toDuration d) ▹ fin
  unparse-span d (rearticulate d₁ _ x₁ x₂) = unparse-span (toDuration d₁ *ᵈ d) x₁ ++ unparse-span (toDuration (d₁ ⁺) *ᵈ d) x₂
  unparse-span {n} d step↑ = (just n , d) ▹ fin
  unparse-span {n} d step↓ = (just n , d) ▹ fin
  unparse-span d (motion↑ size x) = unparse-motion d x
  unparse-span d (motion↓ size x) = unparse-motion d x
  unparse-span d (neighbor↑ d₁ _ x₁ x₂) = unparse-span (toDuration d₁ *ᵈ d) x₁ ++ unparse-span (toDuration (d₁ ⁺) *ᵈ d) x₂
  unparse-span d (neighbor↓ d₁ _ x₁ x₂) = unparse-span (toDuration d₁ *ᵈ d) x₁ ++ unparse-span (toDuration (d₁ ⁺) *ᵈ d) x₂

-- unparse-piece : Section n₁ n₂ → Score
-- unparse-piece (piece start span end) = unparse-post start ++ unparse-span span ++ unparse-post end


obv : {A : Set} → ⦃ a : A ⦄ → A
obv ⦃ a ⦄ = a

𝅘𝅥 = obv
𝄽 = obv

song : Span 0 _
song = neighbor↑ ½ obv 𝅘𝅥 𝅘𝅥

_ : unparse-span 𝅝 song ≡ ?
_ = refl

-- rescale : Score → Score
-- rescale fin = fin
-- rescale ns@((n , d) ▹ ns′) =
--   let smallest = Data.List.foldr _⊔_ d (Data.List.map proj₂ ns′)
--    in Data.List.map (map₂ (_÷ smallest)) ns

-- _▹[_]_ : Span 1ℚ n₁ n₂ → Post _ → Span 1ℚ _ n₃ → Span 1ℚ _ _
-- _▹[_]_ = trans tt tt

-- infixr 4 _▹[_]_

-- ode : Section 2 _
-- Section.start ode = rearticulate 2 obv
-- Section.span ode =
--   motion↑ 2 𝅘𝅥 ▹[ rearticulate _ 𝅘𝅥 ]
--   motion↓ 4 𝅘𝅥 ▹[ rearticulate _ 𝅘𝅥 ]
--   motion↑ 2 𝅘𝅥
-- Section.end ode =
--   rearticulate _ (
--     𝅘𝅥 ▹[ 𝅘𝅥 ]
--     neighbor↓ 𝅘𝅥 (rearticulate _ 𝅘𝅥) 𝅘𝅥)

-- _ : unparse-piece ode ≡ 2 ▹ 2 ▹ 3 ▹ 4 ▹ 4 ▹ 3 ▹ 2 ▹ 1 ▹ 0 ▹ 0 ▹ 1 ▹ 2 ▹ 2 ▹ 1 ▹ 1 ▹ 2 ▹ fin
-- _ = refl


