module Interval where

open import Data.Nat
open import Data.Nat.DivMod
open import Relation.Binary using (Rel)
open import Agda.Primitive
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; cong)
open import Musikal.Classes

private variable
  -- p p₁ p₂ p₃ : Pitch
  n n₁ n₂ n₃ : ℕ

data IntervalCategory : Set where
  repetition : IntervalCategory
  step       : IntervalCategory
  skip       : IntervalCategory

data IntervalName : Set where
  unison second third fourth fifth sixth seventh octave : IntervalName

data Interval : Set where
  p1 m2 M2 m3 M3 p4 tritone p5 m6 M6 m7 M7 : Interval
  8va : Interval → Interval

data DiatonicInterval : Interval → Set where
  p1 : DiatonicInterval p1
  M2 : DiatonicInterval M2
  M3 : DiatonicInterval M3
  p4 : DiatonicInterval p4
  p5 : DiatonicInterval p5
  M6 : DiatonicInterval M6
  M7 : DiatonicInterval M7
  8va : ∀ {i} → DiatonicInterval i → DiatonicInterval (8va i)

pattern p8 = 8va p1

DiatonicInterval? : (i : Interval) → Dec (DiatonicInterval i)
DiatonicInterval? p1 = yes p1
DiatonicInterval? m2 = no λ ()
DiatonicInterval? M2 = yes M2
DiatonicInterval? m3 = no λ ()
DiatonicInterval? M3 = yes M3
DiatonicInterval? p4 = yes p4
DiatonicInterval? tritone = no λ ()
DiatonicInterval? p5 = yes p5
DiatonicInterval? m6 = no λ ()
DiatonicInterval? M6 = yes M6
DiatonicInterval? m7 = no λ ()
DiatonicInterval? M7 = yes M7
DiatonicInterval? (8va i) with DiatonicInterval? i
... | yes z = yes (8va z)
... | no z = no λ { (8va x) → z x }


data Quality : Set where
  minor major perfect : Quality

data IntervalQuality : Interval → Quality → Set where
  p1q : IntervalQuality p1 perfect
  m2q : IntervalQuality m2 minor
  M2q : IntervalQuality M2 major
  m3q : IntervalQuality m3 minor
  M3q : IntervalQuality M3 major
  p4q : IntervalQuality p4 perfect
  p5q : IntervalQuality p5 perfect
  m6q : IntervalQuality m6 minor
  M6q : IntervalQuality M6 major
  m7q : IntervalQuality m7 minor
  M7q : IntervalQuality M7 major
  p8q : IntervalQuality p8 perfect

data IntervalSize : Interval → IntervalName → Set where
  p1n : IntervalSize p1 unison
  m2n : IntervalSize m2 second
  M2n : IntervalSize M2 second
  m3n : IntervalSize m3 third
  M3n : IntervalSize M3 third
  p4n : IntervalSize p4 fourth
  p5n : IntervalSize p5 fifth
  m6n : IntervalSize m6 sixth
  M6n : IntervalSize M6 sixth
  m7n : IntervalSize m7 seventh
  M7n : IntervalSize M7 seventh
  p8n : IntervalSize p8 octave

open import Data.Fin hiding (_+_; _≤_; _≤?_)


intervalSemitones : Interval → ℕ
intervalSemitones p1 = 0
intervalSemitones m2 = 1
intervalSemitones M2 = 2
intervalSemitones m3 = 3
intervalSemitones M3 = 4
intervalSemitones p4 = 5
intervalSemitones tritone = 6
intervalSemitones p5 = 7
intervalSemitones m6 = 8
intervalSemitones M6 = 9
intervalSemitones m7 = 10
intervalSemitones M7 = 11
intervalSemitones (8va i) = 12 + intervalSemitones i

fromIntervalSemitones : ℕ → Interval
fromIntervalSemitones 0 = p1
fromIntervalSemitones 1 = m2
fromIntervalSemitones 2 = M2
fromIntervalSemitones 3 = m3
fromIntervalSemitones 4 = M3
fromIntervalSemitones 5 = p4
fromIntervalSemitones 6 = tritone
fromIntervalSemitones 7 = p5
fromIntervalSemitones 8 = m6
fromIntervalSemitones 9 = M6
fromIntervalSemitones 10 = m7
fromIntervalSemitones 11 = M7
fromIntervalSemitones (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc x))))))))))))
  = 8va (fromIntervalSemitones x)

instance
  ord-Interval : Ord Interval
  Ord._≤_  ord-Interval x y = intervalSemitones x ≤ intervalSemitones y
  Ord._≤?_ ord-Interval x y = intervalSemitones x ≤? intervalSemitones y

data ConsonantInterval : Interval → Set where
  p1 : ConsonantInterval p1
  m3 : ConsonantInterval m3
  M3 : ConsonantInterval M3
  p4 : ConsonantInterval p4  -- only when it's not the lowest note
  p5 : ConsonantInterval p5
  m6 : ConsonantInterval m6
  M6 : ConsonantInterval M6
  octave : ConsonantInterval p8

-- data Adjacency : Rel IntervalName lzero where
--   sym  : ∀ {i j} → Adjacency i j → Adjacency j i
--   adj₁ : Adjacency unison second
--   adj₂ : Adjacency second third
--   adj₃ : Adjacency third fourth
--   adj₄ : Adjacency fourth fifth
--   adj₅ : Adjacency fifth sixth
--   adj₆ : Adjacency sixth seventh
--   adj₇ : Adjacency seventh octave
