module Notes where

open import Data.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin; zero; suc)
open import Agda.Primitive

abstract
  Pitch : Set
  Pitch = ℕ

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

abstract
  Duration : Set
  Duration = ℕ

  _+ᵈ_ : Duration → Duration → Duration
  _+ᵈ_ = _+_

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




