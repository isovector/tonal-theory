module Musikal.Counterpoint where

open import Musikal.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

private variable
  d : 𝔻
  A B : Set
  p : A
  m n x y : Music A

-- _▹→∣_ is the same thing as _▹_
delayed-par : (x y : Music A) → x ▹ y ≡ x ▹→∣ y
delayed-par x y = begin
  x ▹ y                      ≡⟨ sym (cong (_▹ _) (∣-identityʳ x (dur x) ≤-refl)) ⟩
  (x ∣ 𝄽 (dur x)) ▹ y        ≡⟨ sym (cong (_ ▹_) (∣-identityˡ _ 0𝔻 0𝔻≤n)) ⟩
  (x ∣ 𝄽 (dur x)) ▹ (⊘ ∣ y)  ≡⟨ sym (interchange _ _ _ _ refl) ⟩
  x ▹ ⊘ ∣ 𝄽 (dur x) ▹ y      ≡⟨ cong (_∣ 𝄽 (dur x) ▹ y) (▹-identityʳ _) ⟩
  x ∣ 𝄽 (dur x) ▹ y          ∎
  where open ≡-Reasoning

----

-- Now we'd like to show that any piece of music can be considered as
-- a collection of parallel lines of sequential notes.

-- Seq is capable only of expressing sequential music
data Seq (Embed : Music A → Set) : Music A → Set where
  embed : Embed m → Seq Embed m
  𝅘𝅥 : Seq Embed (𝅘𝅥 p d)
  𝄽 : Seq Embed (𝄽 d)
  _▹_ : Seq Embed x → Seq Embed y → Seq Embed (x ▹ y)

-- Par is capable only of expressing parallel music
data Par {A : Set} (Embed : Music A → Set) : Music A → Set where
  embed : Embed m → Par Embed m
  𝅘𝅥 : Par Embed (𝅘𝅥 p d)
  𝄽 : Par Embed (𝄽 d)
  _∣_ : Par Embed x → Par Embed y → Par Embed (x ∣ y)


open import Data.Empty

-- A helper type to bottom out our embedding (in essence saying the `embed`
-- constructor above cannot be used.)
NoFurtherEmbedding : Music A → Set
NoFurtherEmbedding _ = ⊥

-- Parallel lines of sequential music (aka counterpoint)
ParSeq : (A : Set) → Music A → Set
ParSeq A = Par {A = A} (Seq {A = A} NoFurtherEmbedding)

-- Sequences of parallel music (aka sequences of chords)
SeqPar : (A : Set) → Music A → Set
SeqPar A = Seq {A = A} (Par {A = A} NoFurtherEmbedding)

-- Given a ParSeq of m and n, we can give a ParSeq of m ▹→∣ n
_▹→∣ₚ_ : ParSeq A m → ParSeq A n → ParSeq A (m ▹→∣ n)
m ▹→∣ₚ embed x = m ∣ embed (𝄽 ▹ x)
m ▹→∣ₚ 𝅘𝅥       = m ∣ embed (𝄽 ▹ 𝅘𝅥)
m ▹→∣ₚ 𝄽       = m ∣ embed (𝄽 ▹ 𝄽)
_▹→∣ₚ_ {A} {m = mm} m (_∣_ {x} {y} n₁ n₂) = subst (ParSeq A)
  ( begin
    let d = 𝄽 (dur mm) in
    (mm ∣ d ▹ x) ∣ (mm ∣ d ▹ y)  ≡⟨ cong (_∣ (mm ∣ d ▹ y)) (∣-comm _ _) ⟩
    (d ▹ x ∣ mm) ∣ (mm ∣ d ▹ y)  ≡⟨ ∣-assoc _ _ _ ⟩
    d ▹ x ∣ (mm ∣ (mm ∣ d ▹ y))  ≡⟨ cong (d ▹ x ∣_) (sym (∣-assoc _ _ _)) ⟩
    d ▹ x ∣ (mm ∣ mm) ∣ d ▹ y    ≡⟨ cong (λ φ → d ▹ x ∣ φ ∣ d ▹ y) (∣-idem _) ⟩
    d ▹ x ∣ (mm ∣ d ▹ y)         ≡⟨ sym (∣-assoc _ _ _) ⟩
    (d ▹ x ∣ mm) ∣ d ▹ y         ≡⟨ cong (_∣ d ▹ y) (∣-comm _ _) ⟩
    (mm ∣ d ▹ x) ∣ d ▹ y         ≡⟨ ∣-assoc _ _ _ ⟩
    mm ∣ (d ▹ x ∣ d ▹ y)         ≡⟨ cong (mm ∣_) (elim-head _ _ _) ⟩
    mm ∣ d ▹ (x ∣ y)             ∎
  ) (m ▹→∣ₚ n₁ ∣ m ▹→∣ₚ n₂)
  where open ≡-Reasoning

-- Any piece of music can be encoded as a parallel sequence:
asLines : (m : Music A) → ParSeq A m
asLines (𝅘𝅥 p d) = 𝅘𝅥
asLines (𝄽 d) = 𝄽
asLines {A} (m ▹ n) = subst (ParSeq A) (sym (delayed-par _ _)) (asLines m ▹→∣ₚ asLines n)
asLines (m ∣ n) = asLines m ∣ asLines n

open import Data.List

linesFromParSeq : ParSeq A m → List (Music A)
linesFromParSeq {m = m} (embed x) = [ m ]
linesFromParSeq {m = m} 𝅘𝅥 = [ m ]
linesFromParSeq {m = m} 𝄽 = [ m ]
linesFromParSeq (x ∣ y) = linesFromParSeq x ++ linesFromParSeq y

lines : Music A → List (Music A)
lines m = linesFromParSeq (asLines m)


open import Relation.Nullary
open import Data.Unit

-- However, not all music can be encoded as sequential parallel notes:
¬asChords : ¬ ((A : Set) → (m : Music A) → SeqPar A m)
¬asChords f with f ⊤ (𝅘𝅥 tt 1𝔻 ▹ 𝅘𝅥 tt 2𝔻 ∣ 𝅘𝅥 tt 2𝔻 ▹ 𝅘𝅥 tt 1𝔻)
... | embed (embed () ∣ _)

-- Therefore, we are justified in decomposing music into counterpoint, but NOT
-- into sequences of chords.

