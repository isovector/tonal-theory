module Pitch where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin as Fin using (Fin; toℕ; remQuot; inject≤; zero; suc)
open import Agda.Primitive
open import Data.Product
open import Interval

private
  _+ᶠ_ : ∀ {m n} → Fin (suc m) → Fin n → Fin (m + n)
  _+ᶠ_ {m} {n} zero y = inject≤ y (begin
    n      ≤⟨ m≤m+n n m ⟩
    n + m  ≡⟨ +-comm n m ⟩
    m + n  ∎
    )
    where open ≤-Reasoning
  _+ᶠ_ {suc m} {n} (suc x) y = suc (x +ᶠ y)

abstract
  Pitch : Set
  Pitch = ℕ

  bottom : Pitch
  bottom = 0

  _+ᵖ_ : Pitch → ℕ → Pitch
  _+ᵖ_ = _+_

  _aboveᵖ_ : Interval → Pitch → Pitch
  i aboveᵖ p = p + toℕ (intervalSemitones i)

  infixl 5 _+ᵖ_

  PitchClass : Set
  PitchClass = Fin 12

  _aboveᶜ_ : Interval → PitchClass → PitchClass
  i aboveᶜ pc with remQuot 2 (intervalSemitones i +ᶠ pc)
  ... | fst , _ = fst

  pitchClass : Pitch → PitchClass
  pitchClass zero    = zero
  pitchClass (suc p) = m2 aboveᶜ pitchClass p

  record HasPitchClass (p : Pitch) (c : PitchClass) : Set where
    field
      which-octave : ℕ
      equals : which-octave * 12 + toℕ c ≡ p

SamePitchClass : Rel Pitch lzero
SamePitchClass p₁ p₂ = ∃[ c ] HasPitchClass p₁ c × HasPitchClass p₂ c

record InDiatonicCollection (tonic pc : PitchClass) : Set where
  field
    interval : Interval
    is-diatonic : DiatonicInterval interval
    in-collection : interval aboveᶜ tonic ≡ pc

SameDiatonicCollection : Rel Pitch lzero
SameDiatonicCollection p₁ p₂ =
  ∃[ c ] InDiatonicCollection c (pitchClass p₁)
       × InDiatonicCollection c (pitchClass p₂)


