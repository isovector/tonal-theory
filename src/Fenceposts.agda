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
open import Data.Maybe renaming (just to note; nothing to rest)
open import Data.Maybe.Properties using (just-injective)

iterateN : {A : Set} → ℕ → A → (A → A) → A
iterateN zero    b f = b
iterateN (suc n) b f = f (iterateN n b f)

open import Data.Nat.Properties using (+-assoc)

{-# REWRITE +-assoc #-}


open Data.Nat
  renaming (ℕ to Note; zero to base; suc to step; _≤_ to _≤ⁿ_)
  public

open Data.Nat
  renaming (ℕ to Duration; zero to instant; suc to delay; _≤_ to _≤ᵈ_; _+_ to _+ᵈ_; _*_ to _*ᵈ_)
  public

open import Data.Unit using (⊤; tt)

Consonant : Rel Note lzero
Consonant _ _ = ⊤

open import Data.List
  renaming ([] to fin; _∷_ to _▹_)
  using (List; _++_; _∷ʳ_)
  public

private variable
  n n₁ n₂ n₃ : Note
  t t₁ t₂ : Duration
  d d₁ d₂ : Duration

data Direction : Set where
  dir↑ dir↓ : Direction

otherDirection : Direction → Direction
otherDirection dir↑ = dir↓
otherDirection dir↓ = dir↑

private variable
  dir : Direction

infixr 4 _↑<_>_ _↓<_>_


mutual
  data Motion : Direction → ℕ → Rel Note lzero where
    [_]  : Span n₁ n₂ → Motion dir 1 n₁ n₂
    _↑<_>_ : {size : ℕ}
           → Span n₁ (step n₁)
           → Post (step n₁)
           → Motion dir↑ (suc size) (step n₁) n₂
           → Motion dir↑ (suc (suc size)) n₁ n₂
    _↓<_>_ : {size : ℕ}
           → Span (step n₂) n₂
           → Post n₂
           → Motion dir↓ (suc size) n₂ n₁
           → Motion dir↓ (suc (suc size)) (step n₂) n₁

  -- spans are motion
  data Span : Rel Note lzero where
    stay  : Span n n
    step↑ : Span n (step n)
    step↓ : Span (step n) n
    trans : Consonant n₁ n₂ → Consonant n₂ n₃ → Span n₁ n₂ → Post n₂ → Span n₂ n₃ → Span n₁ n₃
    motion↑ : (size : ℕ) → Motion dir↑ size n (iterateN size n step) → Span n (iterateN size n step)
    motion↓ : (size : ℕ) → Motion dir↓ size (iterateN size n step) n → Span (iterateN size n step) n
    neighbor↑ : Span n (step n) → Post (step n) → Span (step n) n → Span n n
    neighbor↓ : Span (step n) n → Post n → Span n (step n) → Span (step n) (step n)

  -- posts are goals
  data Post : Note → Set where
    note : (n : Note) → Post n
    rearticulate : (n : Note) → Span n n → Post n


instance
  inst-[] : ⦃ Span n₁ n₂ ⦄ → Motion dir 1 n₁ n₂
  inst-[] ⦃ x ⦄ = [ x ]

  inst-↑<>
    : ∀ {size}
    → ⦃ Span n₁ (step n₁) ⦄
    → ⦃ Post (step n₁) ⦄
    → ⦃ Motion dir↑ (suc size) (step n₁) n₂ ⦄
    → Motion dir↑ (suc (suc size)) n₁ n₂
  inst-↑<> ⦃ s ⦄ ⦃ p ⦄ ⦃ m ⦄ = s ↑< p > m

  inst-↓<>
    : ∀ {size}
    → ⦃ Span (step n₂) n₂ ⦄
    → ⦃ Post n₂ ⦄
    → ⦃ Motion dir↓ (suc size) n₂ n₁ ⦄
    → Motion dir↓ (suc (suc size)) (step n₂) n₁
  inst-↓<> ⦃ s ⦄ ⦃ p ⦄ ⦃ m ⦄ = s ↓< p > m

  inst-note : Post n
  inst-note = note _

  inst-stay : Span n n
  inst-stay = stay

  inst-step↑ : Span n _
  inst-step↑ = step↑

  inst-step↓ : Span _ n
  inst-step↓ = step↓


postulate
  reverse : ∀ {size} → Motion dir size n₁ n₂ → Motion (otherDirection dir) size n₂ n₁

mutual
  flip : Post n → Post n
  flip (note _) = note _
  flip (rearticulate _ x) = rearticulate _ (syms x)

  syms : Span n₁ n₂ → Span n₂ n₁
  syms stay = stay
  syms step↑ = step↓
  syms step↓ = step↑
  syms (trans x x₁ x₂ x₃ x₄) = trans tt tt (syms x₄) x₃ (syms x₂)
  syms (motion↑ size x) = motion↓ size (reverse x)
  syms (motion↓ size x) = motion↑ size (reverse x)
  syms (neighbor↑ x x₁ x₂) = neighbor↑ (syms x₂) (flip x₁) (syms x)
  syms (neighbor↓ x x₁ x₂) = neighbor↓ (syms x₂) (flip x₁) (syms x)

record Piece : Set where
  constructor piece
  field
    {p₁ p₂} : Note
    start : Post p₁
    span  : Span p₁ p₂
    end   : Post p₂

Score : Set
Score = List Note

mutual
  unparse-motion : ∀ {size} → Motion dir size n₁ n₂ → Score
  unparse-motion [ s ] = unparse-span s
  unparse-motion (s ↑< p > m) = unparse-span s ++ unparse-post p ++ unparse-motion m
  unparse-motion (s ↓< p > m) = unparse-span s ++ unparse-post p ++ unparse-motion m

  unparse-span : Span n₁ n₂ → Score
  unparse-span (trans _ _ s₁ p s₂) = unparse-span s₁ ++ unparse-post p ++ unparse-span s₂
  unparse-span stay = fin
  unparse-span step↑ = fin
  unparse-span step↓ = fin
  unparse-span (motion↑ _ m) = unparse-motion m
  unparse-span (motion↓ _ m) = unparse-motion m
  unparse-span (neighbor↑ s₁ p s₂) = unparse-span s₁ ++ unparse-post p ++ unparse-span s₂
  unparse-span (neighbor↓ s₁ p s₂) = unparse-span s₁ ++ unparse-post p ++ unparse-span s₂

  unparse-post : Post n → Score
  unparse-post (note n) = n ▹ fin
  unparse-post (rearticulate n s) = n ▹ unparse-span s ++ n ▹ fin

unparse-piece : Piece → Score
unparse-piece (piece start span end) = unparse-post start ++ unparse-span span ++ unparse-post end


song : Piece
song = piece (note 0)
             (motion↑ 3 (step↑ ↑< rearticulate _ stay > step↑ ↑< rearticulate _ stay > [ step↑ ]))
             (note _)

_ : unparse-piece song ≡ 0 ▹ 1 ▹ 1 ▹ 2 ▹ 2 ▹ 3 ▹ fin
_ = refl

obv : {A : Set} → ⦃ a : A ⦄ → A
obv ⦃ a ⦄ = a

_▹[_]_ : Span n₁ n₂ → Post _ → Span _ n₃ → Span _ _
_▹[_]_ = trans tt tt

infixr 4 _▹[_]_

ode : Piece
Piece.p₁ ode = 2
Piece.p₂ ode = _
Piece.start ode = rearticulate 2 obv
Piece.span ode =
  motion↑ 2 obv ▹[ rearticulate _ obv ]
  motion↓ 4 obv ▹[ rearticulate _ obv ]
  motion↑ 2 obv
Piece.end ode =
  rearticulate _
    (obv ▹[ obv ] neighbor↓ obv (rearticulate _ obv) obv)

_ : unparse-piece ode ≡ 2 ▹ 2 ▹ 3 ▹ 4 ▹ 4 ▹ 3 ▹ 2 ▹ 1 ▹ 0 ▹ 0 ▹ 1 ▹ 2 ▹ 2 ▹ 1 ▹ 1 ▹ 2 ▹ fin
_ = refl


