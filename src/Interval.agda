module Interval where

open import Data.Nat
open import Data.Nat.DivMod
open import Relation.Binary using (Rel)
open import Agda.Primitive
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

private variable
  -- p p₁ p₂ p₃ : Pitch
  n n₁ n₂ n₃ : ℕ

data IntervalCategory : Set where
  repetition : IntervalCategory
  step       : IntervalCategory
  skip       : IntervalCategory

-- data IsIntervalCategory : Pitch → Pitch → IntervalCategory → Set where
--   repetition : IsIntervalCategory p p repetition
--   step↑m     : IsIntervalCategory p (p +ᵖ 1) step
--   step↑M     : IsIntervalCategory p (p +ᵖ 2) step
--   step↓m     : IsIntervalCategory (p +ᵖ 1) p step
--   step↓M     : IsIntervalCategory (p +ᵖ 2) p step
--   skip↑      : IsIntervalCategory p (p +ᵖ suc (suc (suc n))) skip
--   skip↓      : IsIntervalCategory (p +ᵖ suc (suc (suc n))) p skip

data IntervalName : Set where
  unison second third fourth fifth sixth seventh octave : IntervalName

data Interval : Set where
  p1 m2 M2 m3 M3 p4 tritone p5 m6 M6 m7 M7 p8 : Interval

data DiatonicInterval : Interval → Set where
  p1 : DiatonicInterval p1
  M2 : DiatonicInterval M2
  M3 : DiatonicInterval M3
  p4 : DiatonicInterval p4
  p5 : DiatonicInterval p5
  M6 : DiatonicInterval M6
  M7 : DiatonicInterval M7
  p8 : DiatonicInterval p8

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
DiatonicInterval? p8 = yes p8


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

open import Data.Fin hiding (_+_)


intervalSemitones : Interval → Fin 13
intervalSemitones p1 = fromℕ< {m = 0 } (s≤s z≤n)
intervalSemitones m2 = fromℕ< {m = 1 } (s≤s (s≤s z≤n))
intervalSemitones M2 = fromℕ< {m = 2 } (s≤s (s≤s (s≤s z≤n)))
intervalSemitones m3 = fromℕ< {m = 3 } (s≤s (s≤s (s≤s (s≤s z≤n))))
intervalSemitones M3 = fromℕ< {m = 4 } (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
intervalSemitones p4 = fromℕ< {m = 5 } (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
intervalSemitones tritone = fromℕ< {m = 6} (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
intervalSemitones p5 = fromℕ< {m = 7 } (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
intervalSemitones m6 = fromℕ< {m = 8 } (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
intervalSemitones M6 = fromℕ< {m = 9 } (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
intervalSemitones m7 = fromℕ< {m = 10} (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))
intervalSemitones M7 = fromℕ< {m = 11} (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))
intervalSemitones p8 = fromℕ< {m = 12} (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))

fromIntervalSemitones : Fin 13 → Interval
fromIntervalSemitones zero = p1
fromIntervalSemitones (suc zero) = m2
fromIntervalSemitones (suc (suc zero)) = M2
fromIntervalSemitones (suc (suc (suc zero))) = m3
fromIntervalSemitones (suc (suc (suc (suc zero)))) = M3
fromIntervalSemitones (suc (suc (suc (suc (suc zero))))) = p4
fromIntervalSemitones (suc (suc (suc (suc (suc (suc zero)))))) = tritone
fromIntervalSemitones (suc (suc (suc (suc (suc (suc (suc zero))))))) = p5
fromIntervalSemitones (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = m6
fromIntervalSemitones (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = M6
fromIntervalSemitones (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = m7
fromIntervalSemitones (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = M7
fromIntervalSemitones (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = p8

fromIntervalSemitones≢p8 : ∀ {n} → fromIntervalSemitones (inject₁ n) ≢ p8
fromIntervalSemitones≢p8 {suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))} ()
fromIntervalSemitones≢p8 {suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ())))))))))))} x

data ExtendedInterval : Set where
  ↪    : (i : Interval) → i ≢ p8 → ExtendedInterval
  8va+ : ExtendedInterval → ExtendedInterval

extendedIntervalSemitones : ExtendedInterval → ℕ
extendedIntervalSemitones (↪ x _)  = toℕ (intervalSemitones x)
extendedIntervalSemitones (8va+ x) = 12 + extendedIntervalSemitones x

unextendedInterval : ExtendedInterval → Interval
unextendedInterval (↪ i x) = i
unextendedInterval (8va+ (↪ p1 x)) = p8
unextendedInterval (8va+ (↪ i x))  = i
unextendedInterval (8va+ (8va+ x)) = unextendedInterval (8va+ x)

extendInterval : Interval → ExtendedInterval
extendInterval p1 = ↪ p1 λ ()
extendInterval m2 = ↪ m2 λ ()
extendInterval M2 = ↪ M2 λ ()
extendInterval m3 = ↪ m3 λ ()
extendInterval M3 = ↪ M3 λ ()
extendInterval p4 = ↪ p4 λ ()
extendInterval tritone = ↪ tritone λ ()
extendInterval p5 = ↪ p5 λ ()
extendInterval m6 = ↪ m6 λ ()
extendInterval M6 = ↪ M6 λ ()
extendInterval m7 = ↪ m7 λ ()
extendInterval M7 = ↪ M7 λ ()
extendInterval p8 = 8va+ (↪ p1 λ ())

8vas+ : ℕ → Interval → ExtendedInterval
8vas+ zero i = extendInterval i
8vas+ (suc o) i = 8vas+ o i

toExtendedInterval : ℕ → ExtendedInterval
toExtendedInterval n with n divMod 12
... | result octs remainder _ = 8vas+ octs (fromIntervalSemitones (inject₁ remainder))

data ConsonantInterval : Interval → Set where
  p1 : ConsonantInterval p1
  m3 : ConsonantInterval m3
  M3 : ConsonantInterval M3
  p4 : ConsonantInterval p4  -- only when it's not the lowest note
  p5 : ConsonantInterval p5
  m6 : ConsonantInterval m6
  M6 : ConsonantInterval M6
  p8 : ConsonantInterval p8

-- data Adjacency : Rel IntervalName lzero where
--   sym  : ∀ {i j} → Adjacency i j → Adjacency j i
--   adj₁ : Adjacency unison second
--   adj₂ : Adjacency second third
--   adj₃ : Adjacency third fourth
--   adj₄ : Adjacency fourth fifth
--   adj₅ : Adjacency fifth sixth
--   adj₆ : Adjacency sixth seventh
--   adj₇ : Adjacency seventh octave
