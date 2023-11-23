{-# OPTIONS --rewriting #-}

module Fenceposts where

open import Agda.Builtin.Equality.Rewrite

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel; Decidable; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Function using (Injective)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)

iterateN : {A : Set} → ℕ → A → (A → A) → A
iterateN zero    b f = b
iterateN (suc n) b f = f (iterateN n b f)

open import Data.Nat.Properties using (+-assoc)

{-# REWRITE +-assoc #-}


open Data.Nat
  renaming (ℕ to Note; zero to base; suc to step; _≤_ to _≤ⁿ_)
  public

open import Data.Rational
  renaming (ℚ to Duration; _≥_ to _≥ᵈ_; _+_ to _+ᵈ_; _*_ to _*ᵈ_)

open import Data.Rational.Properties
  renaming (≤-refl to ≤ᵈ-refl)

open import Data.Integer using (1ℤ)

subdivide : ℕ → Duration → Duration
subdivide n d = d *ᵈ (1ℤ / suc n)


open import Data.Unit using (⊤; tt)

Consonant : Rel Note lzero
Consonant _ _ = ⊤

open import Data.List
  renaming ([] to fin; _∷_ to _▹_)
  using (List; _++_; _∷ʳ_)
  public

private variable
  n n₁ n₂ n₃ : Note
  t t₁ t₂ t₃ : Duration
  d d₁ d₂ d₃ : Duration

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
  data Motion (d₁ : Duration) (d₂ : Duration) : Direction → ℕ → Duration → Rel Note lzero where
    [_]  : Span d₁ n₁ n₂ → Motion d₁ d₂ dir 1 d₁ n₁ n₂
    _↑_ : {size : ℕ}
           → Span d₁ n₁ (step n₁)
           → Motion d₂ d₂ dir↑ (suc size) d (step n₁) n₂
           → Motion d₁ d₂ dir↑ (suc (suc size)) (d₁ +ᵈ d) n₁ n₂
    _↓_ : {size : ℕ}
           → Span d₁ (step n₂) n₂
           → Motion d₂ d₂ dir↓ (suc size) d n₂ n₁
           → Motion d₁ d₂ dir↓ (suc (suc size)) (d₁ +ᵈ d) (step n₂) n₁

  -- spans are motion
  data Span : Duration → Rel Note lzero where
    stay : Span d n n
    rest : Span d n n
    rearticulate : d₁ ≥ᵈ d₂ → Span d₁ n₁ n₁ → Span d₂ n₁ n₂ → Span (d₁ +ᵈ d₂) n₁ n₂
    step↑ : Span d n (step n)
    step↓ : Span d (step n) n
    -- trans : Consonant n₁ n₂ → Consonant n₂ n₃ → Span d n₁ n₂ → Post 1ℚ n₂ → Span d n₂ n₃ → Span d n₁ n₃
    motion↑ : (size : ℕ) → Motion d₁ d₂ dir↑ size d n (n ⇑ size) → Span d n (n ⇑ size)
    motion↓ : (size : ℕ) → Motion d₁ d₂ dir↓ size d (n ⇑ size) n → Span d (n ⇑ size) n
    neighbor↑ : d₁ ≥ᵈ d₂ → Span d₁ n (step n) → Span d₂ (step n) n → Span d n n
    neighbor↓ : d₁ ≥ᵈ d₂ → Span d₁ (step n) n → Span d₂ n (step n) → Span d (step n) (step n)

data Section : Duration → Rel Note lzero where
  section : Span d₁ n₁ n₂ → (d₂ : Duration) → Section (d₁ +ᵈ d₂) n₁ n₂


instance
  inst-≥ᵈ : d ≥ᵈ d
  inst-≥ᵈ = ≤ᵈ-refl

  inst-[] : ⦃ Span d n₁ n₂ ⦄ → Motion d d dir 1 d n₁ n₂
  inst-[] ⦃ x ⦄ = [ x ]

  inst-↑<>
    : ∀ {size}
    → ⦃ Span d₁ n₁ (step n₁) ⦄
    → ⦃ Motion d₂ d₂ dir↑ (suc size) d (step n₁) n₂ ⦄
    → Motion d₁ d₂ dir↑ (suc (suc size)) (d₁ +ᵈ d) n₁ n₂
  inst-↑<> ⦃ s ⦄ ⦃ m ⦄ = s ↑ m

  inst-↓<>
    : ∀ {size}
    → ⦃ Span d₁ (step n₂) n₂ ⦄
    → ⦃ Motion d₂ d₂ dir↓ (suc size) d n₂ n₁ ⦄
    → Motion d₁ d₂ dir↓ (suc (suc size)) (d₁ +ᵈ d) (step n₂) n₁
  inst-↓<> ⦃ s ⦄ ⦃ m ⦄ = s ↓ m

  inst-stay : Span d n n
  inst-stay = stay

  inst-step↑ : Span d n _
  inst-step↑ = step↑

  inst-step↓ : Span d _ n
  inst-step↓ = step↓


Score : Set
Score = List (Maybe Note × Duration)

mutual
  unparse-motion : ∀ {size} → Motion d₁ d₂ dir size d n₁ n₂ → Score
  unparse-motion [ s ] = unparse-span s
  unparse-motion (s ↑ m) = unparse-span s ++ unparse-motion m
  unparse-motion (s ↓ m) = unparse-span s ++ unparse-motion m

  unparse-span : Span d n₁ n₂ → Score
  unparse-span {d} {n} stay = (just n , d) ▹ fin
  unparse-span {d} rest = (nothing , d) ▹ fin
  unparse-span (rearticulate _ x₁ x₂) = unparse-span x₁ ++ unparse-span x₂
  unparse-span {d} {n} step↑ = (just n , d) ▹ fin
  unparse-span {d} {n} step↓ = (just n , d) ▹ fin
  unparse-span (motion↑ size x) = unparse-motion x
  unparse-span (motion↓ size x) = unparse-motion x
  unparse-span {d} (neighbor↑ _ x₁ x₂) = unparse-span x₁ ++ unparse-span x₂
  unparse-span {d} (neighbor↓ _ x₁ x₂) = unparse-span x₁ ++ unparse-span x₂

  -- unparse-span stay = fin
  -- unparse-span step↑ = fin
  -- unparse-span step↓ = fin
  -- unparse-span (motion↑ _ m) = unparse-motion m
  -- unparse-span (motion↓ _ m) = unparse-motion m
  -- unparse-span (neighbor↑ s₁ p s₂) = unparse-span s₁ ++ unparse-post p ++ unparse-span s₂
  -- unparse-span (neighbor↓ s₁ p s₂) = unparse-span s₁ ++ unparse-post p ++ unparse-span s₂

-- unparse-piece : Section n₁ n₂ → Score
-- unparse-piece (piece start span end) = unparse-post start ++ unparse-span span ++ unparse-post end


obv : {A : Set} → ⦃ a : A ⦄ → A
obv ⦃ a ⦄ = a

𝅘𝅥 = obv
𝄽 = obv

song : Span 1ℚ 0 _
song = neighbor↑ {d₁ = ½} 𝄽 𝅘𝅥 𝅘𝅥


_ : unparse-span song ≡ (just 0 , mkℚ (Data.Integer.+ 1) 1 _) ▹ (just 1 , mkℚ (Data.Integer.+ 1) 1 _) ▹ fin
_ = refl

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


