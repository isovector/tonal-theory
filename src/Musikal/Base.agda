module Musikal.Base where

open import Relation.Binary.PropositionalEquality
open import Duration public


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
join (𝅘𝅥 ma d) = scale (d * (dur ma ⁻¹)) ma
join (𝄽 d) = 𝄽 d
join (m ▹ n) = join m ▹ join n
join (m ∣ n) = join m ∣ join n

pure : A → Music A
pure a = 𝅘𝅥 a 1𝔻
-- spiritually a monad, if we rescale everything down to 0,1 every time.
-- I think. I hope.

_>>=_ : Music A → (A → Music B) → Music B
m >>= f = join (map f m)

_>>_ : Music A → Music B → Music B
a >> b = a >>= λ _ → b

open import Function using (id; _∘_)

postulate
  map-id : (m : Music A) → map id m ≡ m
  map-∘  : {A B C : Set} (m : Music A)
         → (g : B → C)
         → (f : A → B)
         → map (g ∘ f) m ≡ map g (map f m)

-- join∘pure : (m : Music A) → join (pure m) ≡ m
-- join∘pure (𝅘𝅥 p d) = cong (𝅘𝅥 p) ?
-- join∘pure (𝄽 d)   = cong 𝄽 ?
-- join∘pure (m ▹ n) = ?
-- join∘pure (m ∣ n) = ?


-- scale∘scale : ∀ d d′ (m : Music A) → scale ((d * (d′ ⁻¹)) ⁻¹) m ≡ scale (d′ ⁻¹) (scale (d ⁻¹) m)
-- scale∘scale d d′ (𝅘𝅥 x x₁) = {! !}
-- scale∘scale d d′ (𝄽 x) = cong 𝄽 (
--   begin
--     x * ((d * (d′ ⁻¹)) ⁻¹)
--   ≡⟨ ? ⟩
--     x * ((d ⁻¹ * (d′ ⁻¹) ⁻¹))
--   ≡⟨ ? ⟩
--     x * (d ⁻¹ * d′)
--   ≡⟨ ? ⟩
--     (x * (d ⁻¹)) * (d′ ⁻¹)
--   ∎
--   )
--   where open ≡-Reasoning
-- scale∘scale d d′ (m ▹ m₁) = {! !}
-- scale∘scale d d′ (m ∣ m₁) = {! !}

-- join∘scale : (d : 𝔻) (ma : Music (Music A)) → join (scale (d ⁻¹) ma) ≡ scale (d ⁻¹) (join ma)
-- join∘scale d′ (𝅘𝅥 m d) = scale∘scale d d′ m
-- join∘scale d′ (𝄽 d) = refl
-- join∘scale d′ (m ▹ n) rewrite join∘scale d′ m rewrite join∘scale d′ n = refl
-- join∘scale d′ (m ∣ n) rewrite join∘scale d′ m rewrite join∘scale d′ n = refl

-- join∘join : (m : Music (Music (Music A))) → join (join m) ≡ join (map join m)
-- join∘join (𝅘𝅥 ma d) = ?
-- join∘join (𝄽 x) = refl
-- join∘join (m ▹ n) rewrite join∘join m rewrite join∘join n = refl
-- join∘join (m ∣ n) rewrite join∘join m rewrite join∘join n = refl



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

-- We can delay any piece of music by prepending a rest to it:
delay : 𝔻 → Music A → Music A
delay d = 𝄽 d ▹_

-- We can play one piece of music after another, by in parallel, delaying the
-- second piece by the duration of the first.
_▹→∣_ : Music A → Music A → Music A
m ▹→∣ n = m ∣ delay (dur m) n

infixr 6 _▹→∣_


