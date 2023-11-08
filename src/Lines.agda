{-# OPTIONS --rewriting #-}

module Lines where

open import Data.Nat
open import Pitch
open import Duration
open import Interval
open import Relation.Binary using (Rel)
open import Agda.Primitive

open import Data.List using (List; []; _∷_) public

private variable
  d d₁ d₂ d₃ : Duration
  p p₁ p₂ p₃ : Pitch
  i i₁ i₂ i₃ : Interval
  ci : ConsonantInterval i


data Line : Duration → Set where
  rest  : (d : Duration) → Line d
  note  : Pitch → (d : Duration) → Line d
  -- This might be cheating; should be in a different line; but maybe we can
  -- make an operator that pushes coinciding lines into a stack
  stack
    : (d : Duration)
    → (p : Pitch)
    → (int : Interval)
    → ConsonantInterval int
    → Line d
  _▹_   : Line d₁ → Line d₂ → Line (d₁ +ᵈ d₂)
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
  arpeggiate₁
    : (d₁ : Duration)
    → stack (d₁ +ᵈ d₂) p i ci
    ⇒ note p d₁ ▹ note (i aboveᵖ p) d₂
  arpeggiate₂
    : (d₁ : Duration)
    → stack (d₁ +ᵈ d₂) p i ci
    ⇒ note (i aboveᵖ p) d₁ ▹ note p d₂

  -- p36/2
  -- step-motion
  --   : Consonant p₁ p₂
  --   -- → SameDiatonicCollection p₁ p₂
  --   → note p₁ (d₁ +ᵈ d₂) ▹ note p₂ d₃
  --   ⇒ note {! this half of the line is wrong !} (d₁ +ᵈ d₂) ▹ note p₂ d₃


  -- p37/1
  delay-note
    : note p₁ d₁         ▹ note p₂ (d₂ +ᵈ d₃)
    ⇒ note p₁ (d₁ +ᵈ d₂) ▹ note p₂        d₃

  delay-stack
    : stack  d₁        p i ci ▹ note p₂ (d₂ +ᵈ d₃)
    ⇒ stack (d₁ +ᵈ d₂) p i ci ▹ note p₂        d₃

  delay-rest
    : note p (d₁ +ᵈ d₂)
    ⇒ rest d₁ ▹ note p d₂

  -- Synthetic
  refl
    : l₁ ⇒ l₁

  cong
    : l₁ ⇒ l₁′ → l₂  ⇒ l₂′
    → l₁ ▹ l₂  ⇒ l₁′ ▹ l₂′

  trans
    : l₁ ⇒ l₂
    → l₂ ⇒ l₃
    → l₁ ⇒ l₃

module ⇒-Reasoning {d : Duration} where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)
  open import Relation.Binary using (Preorder; IsPreorder; Setoid)

  ⇒-is-preorder : IsPreorder _≡_ (_⇒_ {d = d})
  IsPreorder.isEquivalence ⇒-is-preorder = Setoid.isEquivalence (setoid _)
  IsPreorder.reflexive ⇒-is-preorder refl = refl
  IsPreorder.trans ⇒-is-preorder = trans

  ⇒-preorder : Preorder lzero lzero lzero
  Preorder.Carrier ⇒-preorder = _
  Preorder._≈_ ⇒-preorder = _
  Preorder._∼_ ⇒-preorder = _
  Preorder.isPreorder ⇒-preorder = ⇒-is-preorder

  open import Relation.Binary.Reasoning.Preorder ⇒-preorder public
    hiding (step-≈)


_ : note A0 (2 measures)
  ⇒ note A0 𝅗𝅥 ▹ note (A0 ♯) 𝅗𝅥 ▹ note A0 𝅝
_ = begin
    note A0 (2 measures)                         ∼⟨ rearticulate 𝅝 ⟩
    note (semitones 0) 𝅝 ▹ note (semitones 0) 𝅝  ∼⟨ neighbor 𝅗𝅥 (A0 ♯) ⟩
    note A0 𝅗𝅥 ▹ note (A0 ♯) 𝅗𝅥 ▹ note A0 𝅝        ∎
  where open ⇒-Reasoning

