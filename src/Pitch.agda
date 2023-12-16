module Pitch where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Relation.Binary using (Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin as Fin using (Fin; toℕ; remQuot; inject≤; zero; suc; fromℕ<)
open import Agda.Primitive
open import Data.Product
open import Interval

data PitchClass : Set where
  A A♯ B C C♯ D D♯ E F F♯ G G♯ : PitchClass

A♭ B♭ B♯ C♭ D♭ E♭ E♯ F♭ G♭  : PitchClass
A♭ = G♯
B♭ = A♯
B♯ = C
C♭ = B
D♭ = C♯
E♭ = D♯
E♯ = F
F♭ = E
G♭ = F♯

fromPitchClass : PitchClass → Fin 12
fromPitchClass C  = zero
fromPitchClass C♯ = suc zero
fromPitchClass D  = suc (suc zero)
fromPitchClass D♯  = suc (suc (suc zero))
fromPitchClass E = suc (suc (suc (suc zero)))
fromPitchClass F  = suc (suc (suc (suc (suc zero))))
fromPitchClass F♯ = suc (suc (suc (suc (suc (suc zero)))))
fromPitchClass G  = suc (suc (suc (suc (suc (suc (suc zero))))))
fromPitchClass G♯  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
fromPitchClass A = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
fromPitchClass A♯  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
fromPitchClass B = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

toPitchClass : Fin 12 → PitchClass
toPitchClass zero = C
toPitchClass (suc zero) = C♯
toPitchClass (suc (suc zero)) = D
toPitchClass (suc (suc (suc zero))) = D♯
toPitchClass (suc (suc (suc (suc zero)))) = E
toPitchClass (suc (suc (suc (suc (suc zero))))) = F
toPitchClass (suc (suc (suc (suc (suc (suc zero)))))) = F♯
toPitchClass (suc (suc (suc (suc (suc (suc (suc zero))))))) = G
toPitchClass (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = G♯
toPitchClass (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = A
toPitchClass (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = A♯
toPitchClass (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = B



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

toNote : PitchClass → ℕ → Pitch
toNote c o = semitones (o * 12 + toℕ (fromPitchClass c))


fromNote : Pitch → PitchClass × ℕ
fromNote (semitones n) with n divMod 12
... | result octs remainder _ = toPitchClass remainder , octs

_♯ : Pitch → Pitch
semitones st ♯ = semitones (suc st)

_♭ : Pitch → Pitch
semitones zero ♭ = semitones zero
semitones (suc st) ♭ = semitones st


A0 C4 : Pitch
A0 = toNote A 0
C4 = toNote C 4


_+ᵖ_ : Pitch → ℕ → Pitch
semitones x +ᵖ y = semitones (x + y)

_aboveᵖ_ : Interval → Pitch → Pitch
i aboveᵖ p = p +ᵖ intervalSemitones i

infixl 5 _+ᵖ_

open import Function using (_∘_)

-- _aboveᶜ_ : Interval → PitchClass → PitchClass
-- _aboveᶜ_ i
--   = toPitchClass
--   ∘ proj₂
--   ∘ remQuot {2} 12
--   ∘ intervalSemitones i +ᶠ_
--   ∘ fromPitchClass

pitchClass : Pitch → PitchClass
pitchClass (semitones n) = toPitchClass (fromℕ< (m%n<n n _))

SamePitchClass : Rel Pitch lzero
SamePitchClass p₁ p₂ = pitchClass p₁ ≡ pitchClass p₂

_≤ᵖ_ : Rel Pitch lzero
semitones x ≤ᵖ semitones y = x ≤ y

_≤ᵖ?_ : Decidable _≤ᵖ_
semitones x ≤ᵖ? semitones y = x ≤? y

-- record InDiatonicCollection (pc tonic : PitchClass) : Set where
--   constructor ∈-diatonic
--   field
--     {interval} : Interval
--     is-diatonic : DiatonicInterval interval
--     in-collection : interval aboveᶜ tonic ≡ pc


-- -- WRONG; why? doesn't use the fact that the tonic is a pitch, not a pitch
-- -- class
-- SameDiatonicCollection : Rel Pitch lzero
-- SameDiatonicCollection p₁ p₂ =
--   ∃[ t ] InDiatonicCollection (pitchClass p₁) (pitchClass t)
--        × InDiatonicCollection (pitchClass p₂) (pitchClass t)

