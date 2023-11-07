{-# OPTIONS --rewriting #-}

module Notes where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc)
open import Agda.Primitive

{-# REWRITE +-assoc #-}


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

data IntervalName : Set where
  unison  : IntervalName
  second  : IntervalName
  third   : IntervalName
  fourth  : IntervalName
  fifth   : IntervalName
  sixth   : IntervalName
  seventh : IntervalName
  octave  : IntervalName

data Adjacency : Rel IntervalName lzero where
  sym  : ∀ {i j} → Adjacency i j → Adjacency j i
  adj₁ : Adjacency unison second
  adj₂ : Adjacency second third
  adj₃ : Adjacency third fourth
  adj₄ : Adjacency fourth fifth
  adj₅ : Adjacency fifth sixth
  adj₆ : Adjacency sixth seventh
  adj₇ : Adjacency seventh octave



data Quality : Set where
  minor major perfect : Quality

data Interval : IntervalName → Quality → Set where
  p1 : Interval unison  perfect
  m2 : Interval second  minor
  M2 : Interval second  major
  m3 : Interval third   minor
  M3 : Interval third   major
  p4 : Interval fourth  perfect
  p5 : Interval fifth   perfect
  m6 : Interval sixth   minor
  M6 : Interval sixth   major
  m7 : Interval seventh minor
  M7 : Interval seventh major
  p8 : Interval octave  perfect

data DiatonicMember : ∀ {i q} → Interval i q → Set where
  p1 : DiatonicMember p1
  M2 : DiatonicMember M2
  M3 : DiatonicMember M3
  p4 : DiatonicMember p4
  p5 : DiatonicMember p5
  M6 : DiatonicMember M6
  M7 : DiatonicMember M7
  p8 : DiatonicMember p8

intervalSize : ∀ {i q} → Interval i q → ℕ
intervalSize p1 = 0
intervalSize m2 = 1
intervalSize M2 = 2
intervalSize m3 = 3
intervalSize M3 = 4
intervalSize p4 = 5
intervalSize p5 = 7
intervalSize m6 = 8
intervalSize M6 = 9
intervalSize m7 = 10
intervalSize M7 = 11
intervalSize p8 = 12


record SameDiatonicCollection (p₁ p₂ : Pitch) : Set where
  field
    tonic : Pitch
    sinterval₁ : ∃₂ Interval
    sinterval₂ : ∃₂ Interval

  interval₁ = proj₂ (proj₂ sinterval₁)
  interval₂ = proj₂ (proj₂ sinterval₂)

  field
    member₁ : DiatonicMember interval₁
    member₂ : DiatonicMember interval₂
    p₁∈ : tonic +ᵖ intervalSize interval₁ ≡ p₁
    p₂∈ : tonic +ᵖ intervalSize interval₂ ≡ p₂


data ConsonantInterval : ∀ {i q} → Interval i q → Set where
  p1 : ConsonantInterval p1
  p8 : ConsonantInterval p8
  p4 : ConsonantInterval p4  -- only when it's not the lowest note
  p5 : ConsonantInterval p5
  m3 : ConsonantInterval m3
  M3 : ConsonantInterval M3
  m6 : ConsonantInterval m6
  M6 : ConsonantInterval M6


data Consonant : Rel Pitch lzero where
  consonant↑ : ∀ {i q} → {int : Interval i q} → ConsonantInterval int → Consonant p (p +ᵖ intervalSize int)
  consonant↓ : ∀ {i q} → {int : Interval i q} → ConsonantInterval int → Consonant (p +ᵖ intervalSize int) p

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
    → SameDiatonicCollection p₁ p₂
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


_ : note bottom (beat *ᵈ 4) ⇒ note 0 1 ▹ note 2 1 ▹ note 0 2
_ = trans (rearticulate 2) (neighbor 1 (bottom +ᵖ 2))

