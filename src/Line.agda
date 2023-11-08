{-# OPTIONS --rewriting --local-confluence-check #-}

module Line where

open import Agda.Builtin.Equality.Rewrite

open import Data.Product using (_,_)
open import Data.Nat
open import Pitch
open import Duration
open import Interval
open import Relation.Binary using (Rel)
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List

private variable
  d d₁ d₂ d₃ : Duration
  p p₁ p₂ p₃ : Pitch
  i i₁ i₂ i₃ : Interval
  ci : ConsonantInterval i

interveningIntervals : ExtendedInterval → ExtendedInterval → List ExtendedInterval
interveningIntervals l h = applyUpTo (λ x → toExtendedInterval (suc (x + extendedIntervalSemitones l))) (extendedIntervalSemitones h ∸ suc (extendedIntervalSemitones l))

open import Function using (_∘_)

interveningPitches : (p₁ p₂ : Pitch) → SameDiatonicCollection p₁ p₂ → List Pitch
interveningPitches _ _ (t , ∈-diatonic {i₁} _ _ , ∈-diatonic {i₂} _ _)
  = map (_aboveˣᵖ (i₁ aboveᵖ t))
        (filter (DiatonicInterval? ∘ unextendedInterval)
                (interveningIntervals (extendInterval i₁)
                                      (extendInterval i₂)))

_ : interveningPitches (toNote E 4) (toNote G 4) (C4 , ∈-diatonic M3 refl , ∈-diatonic p5 refl)
  ≡ M6 aboveᵖ C4 -- NO WRONG NO WRONG
  ∷ []
_ = refl


data Line : Set where
  rest  : (d : Duration) → Line
  note  : Pitch → (d : Duration) → Line
  -- This might be cheating; should be in a different line; but maybe we can
  -- make an operator that pushes coinciding lines into a stack
  stack
    : (d : Duration)
    → (p : Pitch)
    → {int : Interval}
    → ConsonantInterval int
    → Line
  _▹_   : Line → Line → Line
infixr 5 _▹_

duration : Line → Duration
duration (rest d) = d
duration (note x d) = d
duration (stack d p x) = d
duration (x ▹ x₁) = duration x +ᵈ duration x₁

postulate
  ▹-assoc : ∀ l₁ l₂ l₃ → (l₁ ▹ l₂) ▹ l₃ ≡ l₁ ▹ (l₂ ▹ l₃)

-- {-# REWRITE ▹-assoc #-}

joinLine : (l : List Line) → Line → Line
joinLine [] end = end
joinLine (x ∷ l) end = x ▹ joinLine l end




private variable
  l l₁ l₂ l₃ l₁′ l₂′ : Line

infix 2 _⇒_
data _⇒_ : Rel Line lzero where
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
    → (ci : ConsonantInterval i)
    → stack (d₁ +ᵈ d₂) p ci
    ⇒ note p d₁ ▹ note (i aboveᵖ p) d₂
  arpeggiate₂
    : (d₁ : Duration)
    → stack (d₁ +ᵈ d₂) p ci
    ⇒ note (i aboveᵖ p) d₁ ▹ note p d₂

  -- p36/2
  step-motion↑
    : (d₁ : Duration)
    → (d₂ : Duration)
    → {i : Interval}
    → ConsonantInterval i
    → (col : SameDiatonicCollection p (i aboveᵖ p))
    → let pitches = map (λ p → note p d₂) (interveningPitches p (i aboveᵖ p) col) in
      note p (d₁ +ᵈ (d₂ *ᵈ length pitches)) ▹ note (i aboveᵖ p) d₃
    ⇒ note p d₁ ▹ joinLine pitches (note (i aboveᵖ p) d₃)

  -- p37/1
  delay-note
    : note p₁ d₁         ▹ note p₂ (d₂ +ᵈ d₃)
    ⇒ note p₁ (d₁ +ᵈ d₂) ▹ note p₂        d₃

  delay-stack
    : stack  d₁        p ci ▹ note p₂ (d₂ +ᵈ d₃)
    ⇒ stack (d₁ +ᵈ d₂) p ci ▹ note p₂        d₃

  delay-rest
    : note p (d₁ +ᵈ d₂)
    ⇒ rest d₁ ▹ note p d₂

  -- Synthetic
  refl
    : l₁ ⇒ l₁

  assocʳ : (l₁ ▹ l₂) ▹ l₃
         ⇒ l₁ ▹ (l₂ ▹ l₃)

  assocˡ : l₁ ▹ (l₂ ▹ l₃)
         ⇒ (l₁ ▹ l₂) ▹ l₃

  cong
    : l₁ ⇒ l₁′ → l₂  ⇒ l₂′
    → l₁ ▹ l₂  ⇒ l₁′ ▹ l₂′

  trans
    : l₁ ⇒ l₂
    → l₂ ⇒ l₃
    → l₁ ⇒ l₃


congʳ : l₂ ⇒ l₂′
      → l₁ ▹ l₂  ⇒ l₁ ▹ l₂′
congʳ x = cong refl x

congˡ : l₁ ⇒ l₁′
      → l₁ ▹ l₂  ⇒ l₁′ ▹ l₂
congˡ x = cong x refl

module ⇒-Reasoning where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)
  open import Relation.Binary using (Preorder; IsPreorder; Setoid)

  ⇒-is-preorder : IsPreorder _≡_ _⇒_
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

