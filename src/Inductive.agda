module Inductive where

open import Data.Nat using ()
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Duration


-- Pieces of music can be built constructively:
data Music (A : Set) : Set where
  -- A sound, with a given pitch and duration
  𝅘𝅥 : A → 𝔻 → Music A

  -- A period of silence, with a duration
  𝄽 : 𝔻 → Music A

  -- Playing one piece of music after another
  _▹_ : Music A → Music A → Music A

  -- Playing two pieces of music simultaneously
  _∣_ : Music A → Music A → Music A

infixr 5 _∣_
infixr 6 _▹_


private variable
  d : 𝔻
  A B : Set
  p : A
  m n x y : Music A


-- There is a trivial piece of music, namely, a zero amount of silence.
⊘ : Music A
⊘ = 𝄽 0𝔻


-- We can measure the total duration of a piece of music:
dur : Music A → 𝔻
dur (𝅘𝅥 x d) = d
dur (𝄽 d)   = d
dur (x ▹ y) = dur x + dur y  -- The sum of the two durations
dur (x ∣ y) = dur x ⊔ dur y  -- The max of the two durations

map : (A → B) → Music A → Music B
map f (𝅘𝅥 a d) = 𝅘𝅥 (f a) d
map f (𝄽 d) = 𝄽 d
map f (m ▹ n) = map f m ▹ map f n
map f (m ∣ n) = map f m ∣ map f n

scale : 𝔻 → Music A → Music A
scale d′ (𝅘𝅥 a d) = 𝅘𝅥 a (d * d′)
scale d′ (𝄽 d)   = 𝄽 (d * d′)
scale d′ (m ▹ n) = scale d′ m ▹ scale d′ n
scale d′ (m ∣ n) = scale d′ m ∣ scale d′ n

join : Music (Music A) → Music A
join (𝅘𝅥 ma d) = scale d ma
join (𝄽 d) = 𝄽 d
join (m ▹ n) = join m ▹ join n
join (m ∣ n) = join m ∣ join n

pure : A → Music A
pure a = 𝅘𝅥 a 1𝔻

open import Function using (id; _∘_)

postulate
  map-id : (m : Music A) → map id m ≡ m
  map-∘  : {A B C : Set} (m : Music A) → (g : B → C) → (f : A → B) → map (g ∘ f) m ≡ map g (map f m)

-- join∘pure : (m : Music A) → join (pure m) ≡ m
-- join∘pure (𝅘𝅥 p d) = cong (𝅘𝅥 p) (*-identityʳ d)
-- join∘pure (𝄽 d)   = cong 𝄽 (*-identityʳ d)
-- join∘pure (m ▹ n) rewrite join∘pure m rewrite join∘pure n = refl
-- join∘pure (m ∣ n) rewrite join∘pure m rewrite join∘pure n = refl



-- The following axioms exist:
postulate
  -- Any silence can be subdivided into two consecutive silences.
  𝄽-cont : ∀ x y
         → 𝄽 {A = A} (x + y) ≡ (𝄽 x) ▹ (𝄽 y)

  -- ⊘ is a left and right identity for sequencing:
  ▹-identityˡ : (m : Music A)
          → ⊘ ▹ m ≡ m
  ▹-identityʳ : (m : Music A)
          → m ▹ ⊘ ≡ m

  -- Sequencing is associative:
  ▹-assoc : (x y z : Music A)
          → (x ▹ y) ▹ z
          ≡ x ▹ (y ▹ z)

  -- Parallel is commutative
  ∣-comm  : (m n : Music A)
          → m ∣ n ≡ n ∣ m

-- Yanze: I don't understand this axiom
-- I feel there are some property missing from the current encodeing, volume?
  -- Parallel is idempotent
  ∣-idem  : (m : Music A)
          → m ∣ m ≡ m

  -- Any silence is an identity for parallel, so long as it is shorter than the
  -- thing it is in parallel with.
  ∣-identityʳ : ∀ (m : Music A) d
          → d ≤ dur m
          → m ∣ 𝄽 d ≡ m

  -- Parallel is associative
  ∣-assoc : (x y z : Music A)
          → (x ∣ y) ∣ z
          ≡ x ∣ (y ∣ z)

  -- If we have the parallel composition of two sequential things, and the
  -- second notes in each parallel line up in time, then we can reinterpret the
  -- whole thing as a sequence of parallel music:
  interchange
          : (m₁ m₂ n₁ n₂ : Music A)
          → dur m₁ ≡ dur n₁
          → (m₁ ▹ m₂) ∣ (n₁ ▹ n₂)
          ≡ (m₁ ∣ n₁) ▹ (m₂ ∣ n₂)

  -- We can append silence to a parallel composition, so long as it doesn't
  -- change the total duration.
  wait    : ∀ (m n : Music A) d
          → dur n + d ≤ dur m
          → m ∣ n
          ≡ m ∣ (n ▹ 𝄽 d)

-- Given the above, we can derive a left identity for parallel:
∣-identityˡ : ∀ (m : Music A) d → d ≤ dur m → 𝄽 d ∣ m ≡ m
∣-identityˡ m d p = begin
  𝄽 d ∣ m  ≡⟨ ∣-comm _ _ ⟩
  m ∣ 𝄽 d  ≡⟨ ∣-identityʳ _ _ p ⟩
  m        ∎
  where open ≡-Reasoning

-- We can freely duplicate sequential composition into parallel composition:
elim-head : (a b c : Music A) → (a ▹ b) ∣ (a ▹ c) ≡ a ▹ (b ∣ c)
elim-head a b c = begin
  a ▹ b ∣ a ▹ c      ≡⟨ interchange _ _ _ _ refl ⟩
  (a ∣ a) ▹ (b ∣ c)  ≡⟨ cong (_▹ _) (∣-idem _) ⟩
  a ▹ (b ∣ c)        ∎
  where open ≡-Reasoning

----

-- We can delay any piece of music by prepending a rest to it:
delay-by : 𝔻 → Music A → Music A
delay-by d = 𝄽 d ▹_

-- We can play one piece of music after another, by in parallel, delaying the
-- second piece by the duration of the first.
_▹→∣_ : Music A → Music A → Music A
m ▹→∣ n = m ∣ delay-by (dur m) n

infixr 6 _▹→∣_

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


open import Relation.Nullary
open import Data.Unit

2𝔻 = 1𝔻 + 1𝔻

-- However, not all music can be encoded as sequential parallel notes:
¬asChords : ¬ ((A : Set) → (m : Music A) → SeqPar A m)
¬asChords f with f ⊤ (𝅘𝅥 tt 1𝔻 ▹ 𝅘𝅥 tt 2𝔻 ∣ 𝅘𝅥 tt 2𝔻 ▹ 𝅘𝅥 tt 1𝔻)
... | embed (embed () ∣ _)


-- Therefore, we are justified in decomposing music into counterpoint, but NOT
-- into sequences of chords.

