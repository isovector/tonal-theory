{-# OPTIONS --rewriting --local-confluence-check #-}

module Line where

open import Agda.Builtin.Equality.Rewrite

open import Data.Product using (_,_)
open import Data.Nat
open import Data.Nat.Properties
open import Pitch
open import Duration
open import Interval
open import Relation.Binary using (Rel)
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.List

private variable
  d d₁ d₂ d₃ : Duration
  p p₁ p₂ p₃ : Pitch
  i i₁ i₂ i₃ : Interval
  ci : ConsonantInterval i

interveningIntervals : ExtendedInterval → ExtendedInterval → List ExtendedInterval
interveningIntervals l h = applyUpTo (λ x → toExtendedInterval (suc (x + extendedIntervalSemitones l))) (extendedIntervalSemitones h ∸ suc (extendedIntervalSemitones l))

_ : interveningIntervals (extendInterval M3) (extendInterval p5) ≡ ↪ p4 (λ ()) ∷ ↪ tritone (λ ()) ∷ []
_ = refl

open import Function using (_∘_)

-- TODO(sandy): Bad type; the pitch in SameDiatonic is used as an offset, but
-- that is not true of the type itself
interveningPitches : (p₁ p₂ : Pitch) → SameDiatonicCollection p₁ p₂ → List Pitch
interveningPitches _ _ (t , ∈-diatonic {i₁} _ _ , ∈-diatonic {i₂} _ _)
  = map (_aboveˣᵖ t)
        (filter (DiatonicInterval? ∘ unextendedInterval)
                (interveningIntervals (extendInterval i₁)
                                      (extendInterval i₂)))

_ : interveningPitches (toNote E 4) (toNote G 4) (C4 , ∈-diatonic M3 refl , ∈-diatonic p5 refl)
  ≡ p4 aboveᵖ C4
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
  arpeggiate↑
    : (d₁ : Duration)
    → (ci : ConsonantInterval i)
    → stack (d₁ +ᵈ d₂) p ci
    ⇒ note p d₁ ▹ note (i aboveᵖ p) d₂
  arpeggiate↓
    : (d₁ : Duration)
    → (ci : ConsonantInterval i)
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
  step-motion↓
    : (d₁ : Duration)
    → (d₂ : Duration)
    → {i : Interval}
    → ConsonantInterval i
    → (col : SameDiatonicCollection p (i aboveᵖ p))
    → let pitches = reverse (map (λ p → note p d₂) (interveningPitches p (i aboveᵖ p) col)) in
      note (i aboveᵖ p) (d₁ +ᵈ (d₂ *ᵈ length pitches)) ▹ note p d₃
    ⇒ note (i aboveᵖ p) d₁ ▹ joinLine pitches (note p d₃)

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
  refl : l₁ ⇒ l₁

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

-- same-duration : l₁ ⇒ l₂ → duration l₁ ≡ duration l₂
-- same-duration (rearticulate d₁) = refl
-- same-duration (neighbor d₁ p₂) = ?
-- same-duration (arpeggiate↑ d₁ ci) = refl
-- same-duration (arpeggiate↓ d₁ ci) = refl
-- same-duration (step-motion↑ d₁ d₂ x col) = {! !}
-- same-duration (step-motion↓ d₁ d₂ x col) = {! !}
-- same-duration delay-note = ?
-- same-duration delay-stack = ?
-- same-duration delay-rest = refl
-- same-duration refl = {! !}
-- same-duration assocʳ = {! !}
-- same-duration (assocˡ {l₁} {l₂} {l₃}) = sym (+ᵈ-assoc (duration l₁) (duration l₂) (duration l₃))
-- same-duration (cong x x₁)
--   rewrite same-duration x
--   rewrite same-duration x₁
--     = refl
-- same-duration (trans x x₁)
--   rewrite same-duration x
--   rewrite same-duration x₁
--     = refl


congʳ : l₂ ⇒ l₂′
      → l₁ ▹ l₂  ⇒ l₁ ▹ l₂′
congʳ x = cong refl x

congˡ : l₁ ⇒ l₁′
      → l₁ ▹ l₂  ⇒ l₁′ ▹ l₂
congˡ x = cong x refl

_▹▹_ : Line → Line → Line
rest d ▹▹ y = rest d ▹ y
note x d ▹▹ y = note x d ▹ y
stack d p x ▹▹ y = stack d p x ▹ y
(x ▹ y) ▹▹ z = x ▹ (y ▹▹ z)

infixr 4 _▹▹_

reassoced : Line → Line
reassoced (rest d)      = rest d
reassoced (note x d)    = note x d
reassoced (stack d p x) = stack d p x
reassoced (x ▹ y)       = reassoced x ▹▹ reassoced y

postulate
  reassoc : {l : Line} → l ⇒ reassoced l
  -- reassoc {rest d} = refl
  -- reassoc {note x d} = refl
  -- reassoc {stack d p x} = refl
  -- reassoc {l₁ ▹ l₂} = ?

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

