{-# OPTIONS --rewriting #-}

module Fenceposts where

open import Agda.Builtin.Equality.Rewrite

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel; Decidable; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Function using (Injective)
open import Data.Product hiding (map)
open import Data.Nat
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
  using (List; _∷_; []; _++_; _∷ʳ_)
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
n ⇑ s = s + n

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
    rearticulate : (d : Interval) → ⦃ d ≥ᵈ ½ ⦄ → Span n₁ n₁ → Span n₁ n₂ → Span n₁ n₂
    step↑ : Span n (step n)
    step↓ : Span (step n) n
    trans : Consonant n₁ n₂ → Consonant n₂ n₃ → Span n₁ n₂ → Span n₂ n₃ → Span n₁ n₃
    motion↑ : (size : ℕ) → (d : Interval) → Motion dir↑ size n (n ⇑ size) → Span n (n ⇑ size)
    motion↓ : (size : ℕ) → (d : Interval) → Motion dir↓ size (n ⇑ size) n → Span (n ⇑ size) n
    neighbor↑ : (d : Interval) → ⦃ d ≥ᵈ ½ ⦄ → Span n (step n) → Span (step n) n → Span n n
    neighbor↓ : (d : Interval) → ⦃ d ≥ᵈ ½ ⦄ → Span (step n) n → Span n (step n) → Span (step n) (step n)

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
  unparse-span {n} d stay = (just n , toDuration d) ∷ []
  unparse-span d rest = (nothing , toDuration d) ∷ []
  unparse-span d (rearticulate d₁ x₁ x₂) = unparse-span (toDuration d₁ *ᵈ d) x₁ ++ unparse-span (toDuration (d₁ ⁺) *ᵈ d) x₂
  unparse-span {n} d step↑ = (just n , d) ∷ []
  unparse-span {n} d step↓ = (just n , d) ∷ []
  unparse-span d (trans _ _ x₁ x₂) = unparse-span d x₁ ++ unparse-span d x₂
  unparse-span d (motion↑ size i x) = unparse-motion d x
  unparse-span d (motion↓ size i x) = unparse-motion d x
  unparse-span d (neighbor↑ d₁ x₁ x₂) = unparse-span (toDuration d₁ *ᵈ d) x₁ ++ unparse-span (toDuration (d₁ ⁺) *ᵈ d) x₂
  unparse-span d (neighbor↓ d₁ x₁ x₂) = unparse-span (toDuration d₁ *ᵈ d) x₁ ++ unparse-span (toDuration (d₁ ⁺) *ᵈ d) x₂


obv : {A : Set} → ⦃ a : A ⦄ → A
obv ⦃ a ⦄ = a

∙ : ⦃ Span n₁ n₂ ⦄ → Span n₁ n₂
∙ = obv

⇒ : ∀ {sz} → ⦃ Motion dir sz n₁ n₂ ⦄ → Motion dir sz n₁ n₂
⇒ = obv

𝄩 : Interval
𝄩 = ½


𝄽 : Span n n
𝄽 = rest

song : Span 0 _
song = neighbor↑ 𝄩 (rearticulate 𝄩 ∙ ∙) (rearticulate 𝄩 (neighbor↑ 𝄩 ∙ ∙) ∙)

mutual
  motion-complexity : ∀ {sz} → Motion dir sz n₁ n₂ → ℕ
  motion-complexity [ x ] = complexity x
  motion-complexity (x ↑ x₁) = complexity x ⊔ motion-complexity x₁
  motion-complexity (x ↓ x₁) = complexity x ⊔ motion-complexity x₁

  complexity : Span n₁ n₂ → ℕ
  complexity stay = 0
  complexity rest = 0
  complexity (rearticulate d x x₁) = suc (complexity x ⊔ complexity x₁)
  complexity step↑ = 0
  complexity step↓ = 0
  complexity (motion↑ size i x) = suc (motion-complexity x)
  complexity (motion↓ size i x) = suc (motion-complexity x)
  complexity (trans _ _ x x₁) = suc (complexity x ⊔ complexity x₁)
  complexity (neighbor↑ d x x₁) = suc (complexity x ⊔ complexity x₁)
  complexity (neighbor↓ d x x₁) = suc (complexity x ⊔ complexity x₁)

_▹_ : Span n₁ n₂ → Span n₂ n₃ → Span n₁ n₃
_▹_ = trans tt tt

infixr 4 _▹_

ode : Span 2 2
ode = rearticulate 𝄩 ( motion↑ 2 𝄩 ⇒
                     ▹ motion↓ 4 𝄩 ⇒
                     ▹ motion↑ 2 𝄩 ⇒
                     ) (neighbor↓ 𝄩 ∙ (rearticulate 𝄩 ∙ ∙))

_ : complexity ode ≡ 4
_ = refl

-- ode : Section 2 _
-- Section.start ode = rearticulate 2 ob?
-- Section.span ode =
--   motion↑ 2 𝅘𝅥 ▹[ rearticulate _ 𝅘𝅥 ]
--   motion↓ 4 𝅘𝅥 ▹[ rearticulate _ 𝅘𝅥 ]
--   motion↑ 2 𝅘𝅥
-- Section.end ode =
--   rearticulate _ (
--     𝅘𝅥 ▹[ 𝅘𝅥 ]
--     neighbor↓ 𝅘𝅥 (rearticulate _ 𝅘𝅥) 𝅘𝅥)

