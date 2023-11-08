{-# OPTIONS --rewriting #-}

module Notes where

open import Pitch
open import Duration
open import Interval

open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Agda.Primitive

private variable
  d d₁ d₂ d₃ : Duration
  p p₁ p₂ p₃ : Pitch
  n n₁ n₂ n₃ : ℕ



data Consonant : Rel Pitch lzero where
  consonant↑ : {int : Interval} → ConsonantInterval int → Consonant p (int aboveᵖ p)
  consonant↓ : {int : Interval} → ConsonantInterval int → Consonant (int aboveᵖ p) p

data Line : Duration → Set where
  rest : (d : Duration) → Line d
  note : Pitch → (d : Duration) → Line d
  _▹_ : Line d₁ → Line d₂ → Line (d₁ +ᵈ d₂)
infixl 4 _▹_

private variable
  l l₁ l₂ l₃ l₁′ l₂′ : Line d

infix 2 _⇒_
data _⇒_ : {d : Duration} → Rel (Line d) lzero where
  -- p35/1
  rearticulate
    : (d₁ : Duration)
    → note p (d₁    +ᵈ    d₂)
    ⇒ note p  d₁ ▹ note p d₂
  -- p35/2
  neighbor
    : (d₁ : Duration)
    → (p₂ : Pitch)
    → note p₁ (d₁    +ᵈ     d₂)▹ note p₁ d₃
    ⇒ note p₁  d₁ ▹ note p₂ d₂ ▹ note p₁ d₃  -- FOR SOME ADJACENT p₂

  -- p36/1
  -- unclear how to describe arpeggiation; since it's defined as an operator
  -- over multiple lines

  -- p36/2
  step-motion
    : Consonant p₁ p₂
    -- → SameDiatonicCollection p₁ p₂
    → note p₁ (d₁ +ᵈ d₂) ▹ note p₂ d₃
    ⇒ note {! this half of the line is wrong !} (d₁ +ᵈ d₂) ▹ note p₂ d₃


  -- p37/1
  delay
    : note p₁ d₁         ▹ note p₂ (d₂ +ᵈ d₃)
    ⇒ note p₁ (d₁ +ᵈ d₂) ▹ note p₂        d₃
  -- p37/1
  delayR
    : note p (d₁ +ᵈ d₂)
    ⇒ rest d₁ ▹ note p d₂
  cong
    : l₁ ⇒ l₁′ → l₂  ⇒ l₂′
    → l₁ ▹ l₂  ⇒ l₁′ ▹ l₂′
  trans
    : l₁ ⇒ l₂
    → l₂ ⇒ l₃
    → l₁ ⇒ l₃


_ : note A0 (2 measures)
  ⇒ note A0 𝅗𝅥 ▹ note (A0 ♯) 𝅗𝅥 ▹ note A0 𝅝
_ = trans (rearticulate 𝅝) (neighbor 𝅗𝅥 (A0 ♯))

