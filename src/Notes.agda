module Notes where

open import Data.Nat
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc)
open import Agda.Primitive

Pitch : Set
Pitch = ℕ

bottom : Pitch
bottom = 0

_+ᵖ_ : Pitch → ℕ → Pitch
_+ᵖ_ = _+_

record SamePitchClass (pitch₁ pitch₂ : Pitch) : Set where
  field
    octave₁ octave₂ : Pitch
    same-class : octave₁ * 12 + pitch₁ ≡ octave₂ * 12 + pitch₂

PitchClass : Set
PitchClass = Fin 12

pattern s n = suc n
toPitchClass : Pitch → PitchClass
toPitchClass zero = zero
toPitchClass (s zero) = s zero
toPitchClass (s (s zero)) = s (s zero)
toPitchClass (s (s (s zero))) = s (s (s zero))
toPitchClass (s (s (s (s zero)))) = s (s (s (s zero)))
toPitchClass (s (s (s (s (s zero))))) = s (s (s (s (s zero))))
toPitchClass (s (s (s (s (s (s zero)))))) = s (s (s (s (s (s zero)))))
toPitchClass (s (s (s (s (s (s (s zero))))))) = s (s (s (s (s (s (s zero))))))
toPitchClass (s (s (s (s (s (s (s (s zero)))))))) = s (s (s (s (s (s (s (s zero)))))))
toPitchClass (s (s (s (s (s (s (s (s (s zero))))))))) = s (s (s (s (s (s (s (s (s zero))))))))
toPitchClass (s (s (s (s (s (s (s (s (s (s zero)))))))))) = s (s (s (s (s (s (s (s (s (s zero)))))))))
toPitchClass (s (s (s (s (s (s (s (s (s (s (s zero))))))))))) = s (s (s (s (s (s (s (s (s (s (s zero))))))))))
toPitchClass (s (s (s (s (s (s (s (s (s (s (s (s x)))))))))))) = toPitchClass x

postulate
  toPitchClass⊃SamePitchClass : (x y : Pitch) → toPitchClass x ≡ toPitchClass y → SamePitchClass x y

data DiatonicMember : Set where
  d1 d2 d3 d4 d5 d6 d7 : DiatonicMember

Duration : Set
Duration = ℕ

beat : Duration
beat = 1

_+ᵈ_ : Duration → Duration → Duration
_+ᵈ_ = _+_

_*ᵈ_ : Duration → ℕ → Duration
_*ᵈ_ = _*_

infixl 4 _+ᵈ_

private variable
  d d₁ d₂ d₃ : Duration
  p p₁ p₂ p₃ : Pitch
  n n₁ n₂ n₃ : ℕ

data IntervalCategory : Set where
  repetition : IntervalCategory
  step       : IntervalCategory
  skip       : IntervalCategory

data IntervalCategoryProof : Pitch → Pitch → IntervalCategory → Set where
  repetition : IntervalCategoryProof p p repetition
  step↑m     : IntervalCategoryProof p (p +ᵖ 1) step
  step↑M     : IntervalCategoryProof p (p +ᵖ 2) step
  step↓m     : IntervalCategoryProof (p +ᵖ 1) p step
  step↓M     : IntervalCategoryProof (p +ᵖ 2) p step
  skip↑      : IntervalCategoryProof p (p +ᵖ suc (suc (suc n))) skip
  skip↓      : IntervalCategoryProof (p +ᵖ suc (suc (suc n))) p skip

data IntervalSize : Set where
  unison  : IntervalSize
  second  : IntervalSize
  third   : IntervalSize
  fourth  : IntervalSize
  fifth   : IntervalSize
  sixth   : IntervalSize
  seventh : IntervalSize
  octave  : IntervalSize

data Quality : Set where
  minor major perfect : Quality

data IntervalDef : IntervalSize → Quality → ℕ → Set where
  p1 : IntervalDef unison  perfect 0
  m2 : IntervalDef second  minor   1
  M2 : IntervalDef second  major   2
  m3 : IntervalDef third   minor   3
  M3 : IntervalDef third   major   4
  p4 : IntervalDef fourth  perfect 5
  p5 : IntervalDef fifth   perfect 7
  m6 : IntervalDef sixth   minor   8
  M6 : IntervalDef sixth   major   9
  m7 : IntervalDef seventh minor   10
  M7 : IntervalDef seventh major   11
  p8 : IntervalDef octave  perfect 12

data ConsonantInterval : ∀ {i q n} → IntervalDef i q n → Set where
  p1 : ConsonantInterval p1
  p8 : ConsonantInterval p8
  p4 : ConsonantInterval p4  -- only when it's not the lowest note
  p5 : ConsonantInterval p5
  m3 : ConsonantInterval m3
  M3 : ConsonantInterval M3
  m6 : ConsonantInterval m6
  M6 : ConsonantInterval M6


data Consonant : Rel Pitch lzero where
  consonant↑ : ∀ {i q n} → (int : IntervalDef i q n) → ConsonantInterval int → Consonant p (p +ᵖ n)
  consonant↓ : ∀ {i q n} → (int : IntervalDef i q n) → ConsonantInterval int → Consonant (p +ᵖ n) p

data Line : Duration → Set where
  note : Pitch → (d : Duration) → Line d
  _▹_ : Line d₁ → Line d₂ → Line (d₁ +ᵈ d₂)
infixl 4 _▹_

private variable
  l l₁ l₂ l₃ l₁′ l₂′ : Line d

infix 2 _⇒_
data _⇒_ : {d : Duration} → Rel (Line d) lzero where
  rearticulate : (d₁ : Duration)
               → note p (d₁    +ᵈ    d₂)
               ⇒ note p  d₁ ▹ note p d₂
  neighbor : (d₁ : Duration)
           → (p₂ : Pitch)
           → note p₁ (d₁    +ᵈ     d₂)▹ note p₁ d₃
           ⇒ note p₁  d₁ ▹ note p₂ d₂ ▹ note p₁ d₃  -- FOR SOME ADJACENT p₂
  -- unclear how to describe arpeggiation; since it's defined as an operator
  -- over multiple lines
  cong : l₁ ⇒ l₁′ → l₂  ⇒ l₂′
       → l₁ ▹ l₂  ⇒ l₁′ ▹ l₂′
  trans : l₁ ⇒ l₂ → l₂ ⇒ l₃ → l₁ ⇒ l₃


test : note bottom (beat *ᵈ 4) ⇒ note 0 1 ▹ note 2 1 ▹ note 0 2
test = trans (rearticulate 2) (neighbor 1 (bottom +ᵖ 2))

