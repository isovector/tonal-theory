module Inductive where

open import Data.Nat
open import Data.Nat.Properties
open Data.Nat renaming (ℕ to Pitch)
open import Relation.Binary.PropositionalEquality hiding ([_])


-- Pieces of music can be built constructively:
data Music : Set where
  -- A sound, with a given pitch and duration
  𝅘𝅥 : Pitch → ℕ → Music

  -- A period of silence, with a duration
  𝄽 : ℕ → Music

  -- Playing one piece of music after another
  _▹_ : Music → Music → Music

  -- Playing two pieces of music simultaneously
  _∣_ : Music → Music → Music

infixr 5 _∣_
infixr 6 _▹_


private variable
  p : Pitch
  d : ℕ
  m n x y : Music


-- There is a trivial piece of music, namely, a zero amount of silence.
⊘ : Music
⊘ = 𝄽 0


-- We can measure the total duration of a piece of music:
dur : Music → ℕ
dur (𝅘𝅥 x d) = d
dur (𝄽 d)   = d
dur (x ▹ y) = dur x + dur y  -- The sum of the two durations
dur (x ∣ y) = dur x ⊔ dur y  -- The max of the two durations


-- The following axioms exist:
postulate
  -- Any silence can be subdivided into two consecutive silences.
  𝄽-cont : ∀ x y
         → 𝄽(x + y) ≡ (𝄽 x) ▹ (𝄽 y)

  -- ⊘ is a left and right identity for sequencing:
  ▹-identityˡ : ∀ m
          → ⊘ ▹ m ≡ m
  ▹-identityʳ : ∀ m
          → m ▹ ⊘ ≡ m

  -- Sequencing is associative:
  ▹-assoc : ∀ x y z
          → (x ▹ y) ▹ z
          ≡ x ▹ (y ▹ z)

  -- Parallel is commutative
  ∣-comm  : ∀ m n
          → m ∣ n ≡ n ∣ m

  -- Parallel is idempotent
  ∣-idem  : ∀ m
          → m ∣ m ≡ m

  -- Any silence is an identity for parallel, so long as it is shorter than the
  -- thing it is in parallel with.
  ∣-identityʳ : ∀ m d
          → d ≤ dur m
          → m ∣ 𝄽 d ≡ m

  -- Parallel is associative
  ∣-assoc : ∀ x y z
          → (x ∣ y) ∣ z
          ≡ x ∣ (y ∣ z)

  -- If we have the parallel composition of two sequential things, and the
  -- second notes in each parallel line up in time, then we can reinterpret the
  -- whole thing as a sequence of parallel music:
  interchange
          : ∀ m₁ m₂ n₁ n₂
          → dur m₁ ≡ dur n₁
          → (m₁ ▹ m₂) ∣ (n₁ ▹ n₂)
          ≡ (m₁ ∣ n₁) ▹ (m₂ ∣ n₂)

  -- We can append silence to a parallel composition, so long as it doesn't
  -- change the total duration.
  wait    : ∀ m n d
          → dur n + d ≤ dur m
          → m ∣ n
          ≡ m ∣ (n ▹ 𝄽 d)

-- Given the above, we can derive a left identity for parallel:
∣-identityˡ : ∀ m d → d ≤ dur m → 𝄽 d ∣ m ≡ m
∣-identityˡ m d p = begin
  𝄽 d ∣ m  ≡⟨ ∣-comm _ _ ⟩
  m ∣ 𝄽 d  ≡⟨ ∣-identityʳ _ _ p ⟩
  m        ∎
  where open ≡-Reasoning

-- We can freely duplicate sequential composition into parallel composition:
elim-head : (a b c : Music) → (a ▹ b) ∣ (a ▹ c) ≡ a ▹ (b ∣ c)
elim-head a b c = begin
  a ▹ b ∣ a ▹ c      ≡⟨ interchange _ _ _ _ refl ⟩
  (a ∣ a) ▹ (b ∣ c)  ≡⟨ cong (_▹ _) (∣-idem _) ⟩
  a ▹ (b ∣ c)        ∎
  where open ≡-Reasoning

----

-- We can delay any piece of music by prepending a rest to it:
delay-by : ℕ → Music → Music
delay-by d = 𝄽 d ▹_

-- We can play one piece of music after another, by in parallel, delaying the
-- second piece by the duration of the first.
_▹→∣_ : Music → Music → Music
m ▹→∣ n = m ∣ delay-by (dur m) n

infixr 6 _▹→∣_

-- _▹→∣_ is the same thing as _▹_
delayed-par : ∀ x y → x ▹ y ≡ x ▹→∣ y
delayed-par x y = begin
  x ▹ y                      ≡⟨ sym (cong (_▹ _) (∣-identityʳ x (dur x) ≤-refl)) ⟩
  (x ∣ 𝄽 (dur x)) ▹ y        ≡⟨ sym (cong (_ ▹_) (∣-identityˡ _ 0 z≤n)) ⟩
  (x ∣ 𝄽 (dur x)) ▹ (⊘ ∣ y)  ≡⟨ sym (interchange _ _ _ _ refl) ⟩
  x ▹ ⊘ ∣ 𝄽 (dur x) ▹ y      ≡⟨ cong (_∣ 𝄽 (dur x) ▹ y) (▹-identityʳ _) ⟩
  x ∣ 𝄽 (dur x) ▹ y          ∎
  where open ≡-Reasoning

----

-- Now we'd like to show that any piece of music can be considered as
-- a collection of parallel lines of sequential notes.

-- Seq is capable only of expressing sequential music
data Seq (Embed : Music → Set) : Music → Set where
  embed : Embed m → Seq Embed m
  𝅘𝅥 : Seq Embed (𝅘𝅥 p d)
  𝄽 : Seq Embed (𝄽 d)
  _▹_ : Seq Embed x → Seq Embed y → Seq Embed (x ▹ y)

-- Par is capable only of expressing parallel music
data Par (Embed : Music → Set) : Music → Set where
  embed : Embed m → Par Embed m
  𝅘𝅥 : Par Embed (𝅘𝅥 p d)
  𝄽 : Par Embed (𝄽 d)
  _∣_ : Par Embed x → Par Embed y → Par Embed (x ∣ y)


open import Data.Empty

-- A helper type to bottom out our embedding (in essence saying the `embed`
-- constructor above cannot be used.)
NoFurtherEmbedding : Music → Set
NoFurtherEmbedding _ = ⊥

-- Parallel lines of sequential music (aka counterpoint)
ParSeq : Music → Set
ParSeq = Par (Seq NoFurtherEmbedding)

-- Sequences of parallel music (aka sequences of chords)
SeqPar : Music → Set
SeqPar = Seq (Par NoFurtherEmbedding)

-- Given a ParSeq of m and n, we can give a ParSeq of m ▹→∣ n
_▹→∣ₚ_ : ParSeq m → ParSeq n → ParSeq (m ▹→∣ n)
m ▹→∣ₚ embed x = m ∣ embed (𝄽 ▹ x)
m ▹→∣ₚ 𝅘𝅥 = m ∣ embed (𝄽 ▹ 𝅘𝅥)
m ▹→∣ₚ 𝄽 = m ∣ embed (𝄽 ▹ 𝄽)
_▹→∣ₚ_ {mm} m (_∣_ {x} {y} n₁ n₂) = subst ParSeq
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
asLines : (m : Music) → ParSeq m
asLines (𝅘𝅥 p d) = 𝅘𝅥
asLines (𝄽 d) = 𝄽
asLines (m ▹ n) = subst ParSeq (sym (delayed-par _ _)) (asLines m ▹→∣ₚ asLines n)
asLines (m ∣ n) = asLines m ∣ asLines n


open import Relation.Nullary

-- However, not all music can be encoded as sequential parallel notes:
¬asChords : ¬ ((m : Music) → SeqPar m)
¬asChords f with f (𝅘𝅥 1 1 ▹ 𝅘𝅥 1 2 ∣ 𝅘𝅥 2 2 ▹ 𝅘𝅥 2 1)
... | embed (embed () ∣ _)


-- Therefore, we are justified in decomposing music into counterpoint, but NOT
-- into sequences of chords.

