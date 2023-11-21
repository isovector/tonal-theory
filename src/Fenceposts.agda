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


postulate
  Consonant : Rel Note lzero

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
           → Motion dir↓ (suc size) (step n₂) n₂
           → Motion dir↓ (suc (suc size)) n₂ n₁

  data Span : Rel Note lzero where
    empty : Span n₁ n₂
    trans : Consonant n₁ n₂ → Consonant n₂ n₃ → Span n₁ n₂ → Post n₂ → Span n₂ n₃ → Span n₁ n₃
    motion↑ : (size : ℕ) → Motion dir↑ size n (iterateN size n step) → Span n (iterateN size n step)
    motion↓ : (size : ℕ) → Motion dir↓ size (iterateN size n step) n → Span (iterateN size n step) n
    neighbor↑ : Span n (step n) → Post (step n) → Span (step n) n → Span n n
    neighbor↓ : Span (step n) n → Post n → Span n (step n) → Span (step n) (step n)

  data Post : Note → Set where
    note : (n : Note) → Post n
    rearticulate : (n : Note) → Span n n → Post n

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
  unparse-span empty = fin
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
             (motion↑ 2 (empty ↑< rearticulate _ empty > [ empty ]))
             (note 2)

_ : unparse-piece song ≡ ?
_ = refl


