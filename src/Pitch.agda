module Pitch where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin as Fin using (Fin; toℕ; remQuot; inject≤; zero; suc; fromℕ<)
open import Agda.Primitive
open import Data.Product
open import Interval

data PitchClass : Set where
  A A♯ B C C♯ D D♯ E F F♯ G G♯ : PitchClass

A♭ = G♯
B♭ = A♯
B♯ = C
C♭ = B
D♭ = C♯
E♭ = D♯
E♯ = F
F♭ = E
G♭ = F♯

private
  toFin12 : PitchClass → Fin 12
  toFin12 A  = zero
  toFin12 A♯ = suc zero
  toFin12 B  = suc (suc zero)
  toFin12 C  = suc (suc (suc zero))
  toFin12 C♯ = suc (suc (suc (suc zero)))
  toFin12 D  = suc (suc (suc (suc (suc zero))))
  toFin12 D♯ = suc (suc (suc (suc (suc (suc zero)))))
  toFin12 E  = suc (suc (suc (suc (suc (suc (suc zero))))))
  toFin12 F  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  toFin12 F♯ = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  toFin12 G  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  toFin12 G♯ = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

  fromFin12 : Fin 12 → PitchClass
  fromFin12 zero = A
  fromFin12 (suc zero) = A♯
  fromFin12 (suc (suc zero)) = B
  fromFin12 (suc (suc (suc zero))) = C
  fromFin12 (suc (suc (suc (suc zero)))) = C♯
  fromFin12 (suc (suc (suc (suc (suc zero))))) = D
  fromFin12 (suc (suc (suc (suc (suc (suc zero)))))) = D♯
  fromFin12 (suc (suc (suc (suc (suc (suc (suc zero))))))) = E
  fromFin12 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = F
  fromFin12 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = F♯
  fromFin12 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = G
  fromFin12 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = G♯



private
  _+ᶠ_ : ∀ {m n} → Fin (suc m) → Fin n → Fin (m + n)
  _+ᶠ_ {m} {n} zero y = inject≤ y (begin
    n      ≤⟨ m≤m+n n m ⟩
    n + m  ≡⟨ +-comm n m ⟩
    m + n  ∎
    )
    where open ≤-Reasoning
  _+ᶠ_ {suc m} {n} (suc x) y = suc (x +ᶠ y)


record Pitch : Set where
  constructor semitones
  field
    getSemitones : ℕ

note : PitchClass → ℕ → Pitch
note c o = semitones (o * 12 + toℕ (toFin12 c))


A0 C4 : Pitch
A0 = note A 0
C4 = note C 4


_+ᵖ_ : Pitch → ℕ → Pitch
semitones x +ᵖ y = semitones (x + y)

_aboveᵖ_ : Interval → Pitch → Pitch
i aboveᵖ p = p +ᵖ toℕ (intervalSemitones i)

infixl 5 _+ᵖ_

_aboveᶜ_ : Interval → PitchClass → PitchClass
i aboveᶜ pc with remQuot {2} 12 (intervalSemitones i +ᶠ toFin12 pc)
... | _ , snd = fromFin12 snd

pitchClass : Pitch → PitchClass
pitchClass (semitones n) = fromFin12 (fromℕ< (m%n<n n _))

SamePitchClass : Rel Pitch lzero
SamePitchClass p₁ p₂ = pitchClass p₁ ≡ pitchClass p₂

record InDiatonicCollection (pc tonic : PitchClass) : Set where
  field
    interval : Interval
    is-diatonic : DiatonicInterval interval
    in-collection : interval aboveᶜ tonic ≡ pc

SameDiatonicCollection : Rel Pitch lzero
SameDiatonicCollection p₁ p₂ =
  ∃[ c ] InDiatonicCollection (pitchClass p₁) c
       × InDiatonicCollection (pitchClass p₂) c

