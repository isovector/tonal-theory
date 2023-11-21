{-# OPTIONS --rewriting #-}

module TotalOrderPitch where

open import Agda.Builtin.Equality.Rewrite

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel; Decidable; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Function using (Injective)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Maybe renaming (just to note; nothing to rest)
open import Data.Maybe.Properties using (just-injective)

iterateN : {A : Set} → ℕ → A → (A → A) → A
iterateN zero    b f = b
iterateN (suc n) b f = f (iterateN n b f)

open import Data.Nat.Properties using (+-assoc)

{-# REWRITE +-assoc #-}


open Data.Nat
  renaming (ℕ to Note; zero to base; suc to step; _≤_ to _≤ⁿ_)
  public

open Data.Nat
  renaming (ℕ to Duration; zero to instant; suc to delay; _≤_ to _≤ᵈ_; _+_ to _+ᵈ_; _*_ to _*ᵈ_)
  public


record UpInterval (n₁ n₂ : Note) : Set where
  constructor interval
  field
    size : ℕ
    is-up-interval : iterateN size n₁ step ≡ n₂

Interval : Rel Note lzero
Interval n₁ n₂ = UpInterval n₁ n₂ ⊎ UpInterval n₂ n₁

postulate
  intervalBetween : (n₁ n₂ : Note) → Interval n₁ n₂

postulate
  Pitch : Set
  _≤ᵖ_ : Rel Pitch lzero
  toPitch : Note → Pitch
  toPitch-monotonic : ∀ {x y} → x ≤ⁿ y → toPitch x ≤ᵖ toPitch y

  Consonant : Rel Note lzero

open import Data.List
  renaming ([] to fin; _∷_ to _▹_)
  public

Score : Set
Score = List (Maybe Note × Duration)

Passage : Set₁
Passage = Rel (Note × Duration) lzero

private variable
  n n₁ n₂ n₃ : Note
  p p₁ p₂ : Pitch
  t t₁ t₂ : Duration
  d d₁ d₂ : Duration

data IsNeighbor : Rel Note lzero where
  step↑ : IsNeighbor n (step n)
  step↓ : IsNeighbor (step n) n

data Direction : Set where
  dir↑ dir↓ : Direction

private variable
  dir : Direction

infixr 4 _↑_ _↓_

mutual
  data Motion (d : Duration) : Direction → ℕ → Note × Duration → Set where
    []  : Motion d dir 0 (n , t)
    _↑_ : {size : ℕ}
        → StructuredSong (n , t) (step n , t +ᵈ d)
        → Motion d dir↑ size        (step n , t +ᵈ d)
        → Motion d dir↑ (suc size)  (n , t)
    _↓_ : {size : ℕ}
        → StructuredSong (step n , t) (n , t +ᵈ d)
        → Motion d dir↓ size             (n , t +ᵈ d)
        → Motion d dir↓ (suc size)       (step n , t)

  data StructuredSong : Passage where
    note  : StructuredSong (n₁ , t)  (n₂ , t +ᵈ d)
    rest  : StructuredSong (n , t)  (n , t +ᵈ d)
    rearticulate
      : (d₁ d₂ : Duration) → d₂ ≤ d₁
      → StructuredSong (n₁ , t)       (n₁ , t +ᵈ d₁)
      → StructuredSong (n₂ , t +ᵈ d₁) (n₂ , t +ᵈ d₁ +ᵈ d₂)
      → StructuredSong (n₁ , t)       (n₂ , t +ᵈ d₁ +ᵈ d₂)
    neighbor
      : (d₁ d₂ : Duration) → d₂ ≤ d₁
      → IsNeighbor n₁ n₂
      → StructuredSong (n₁ , t)       (n₂ , t +ᵈ d₁)
      → StructuredSong (n₂ , t +ᵈ d₁) (n₁ , t +ᵈ d₁ +ᵈ d₂)
      → StructuredSong (n₁ , t)       (n₁ , t +ᵈ d₁ +ᵈ d₂)
    arpeggiate
      : (d₁ d₂ : Duration) → d₂ ≤ d₁
      → Consonant n₁ n₂
      → StructuredSong (n₁ , t)       (n₂ , t +ᵈ d₁)
      → StructuredSong (n₂ , t +ᵈ d₁) (n₁ , t +ᵈ d₁ +ᵈ d₂)
      → StructuredSong (n₁ , t)       (n₁ , t +ᵈ d₁ +ᵈ d₂)
    motion↑
      : (size : ℕ)
      → (d : Duration)
      → Motion d dir↑ size (n , t)
      -- needs a structured song at the end for the last note
      → StructuredSong (n , t) (iterateN size n step , t +ᵈ (d *ᵈ size))
    motion↓
      : (size : ℕ)
      → (d : Duration)
      → Motion d dir↓ size (iterateN size n step , t)
      -- needs a structured song at the end for the last note
      → StructuredSong (iterateN size n step , t) (n , t +ᵈ (d *ᵈ size))

mutual
  unparseMotion : ∀ {d dir sz s} → Motion d dir sz s → Score
  unparseMotion [] = fin
  unparseMotion (x ↑ x₁) = unparse x ++ unparseMotion x₁
  unparseMotion (x ↓ x₁) = unparse x ++ unparseMotion x₁

  unparse : StructuredSong (n₁ , t₁) (n₂ , t₂) → Score
  unparse {n₁ = n₁} (note {d = d}) = (note n₁ , d) ▹ fin
  unparse (rest {d = d}) = (rest , d) ▹ fin
  unparse (rearticulate d₁ d₂ x x₁ x₂) = unparse x₁ ++ unparse x₂
  unparse (neighbor d₁ d₂ x x₁ x₂ x₃)    = unparse x₂ ++ unparse x₃
  unparse (arpeggiate d₁ d₂ x x₁ x₂ x₃)  = unparse x₂ ++ unparse x₃
  unparse {n₂ = n₂} (motion↑ size d x) = unparseMotion x
  unparse {n₂ = n₂} (motion↓ size d x) = unparseMotion x

notesOf : ∀ {x t n} → StructuredSong x (n , t) → List Note
notesOf {n = n} ss = mapMaybe (λ { x → x }) (Data.List.map proj₁ (unparse ss))


reart : StructuredSong (n₁ , t) (n₂ , _)
reart = rearticulate 1 _ (s≤s z≤n) note note

basic-step : StructuredSong (1 , 0) (base , 2)
basic-step =
  motion↓ 1 2
    (   reart
      ↓ []
    )


_ : unparse basic-step ≡ (note 1 , 1) ▹ (note 0 , 1) ▹ fin
_ = refl

-- data Relationship : Rel Note lzero where
--   rearticulation : Relationship n n
--   motion↑ : Relationship n (step n)
--   motion↓ : Relationship (step n) n

-- -- open import Data.Maybe.Relation.Binary.Connected hiding (sym; refl)
-- -- open import Data.List.Relation.Unary.Linked hiding (head)
-- -- open import Data.List.Relation.Unary.Linked.Properties using (++⁺)
-- -- open import Data.List.Properties using (map-++-commute)

-- -- head-is : ∀ {x} → (ss : StructuredSong (n , t₁) x) → (m : Note) → head (notesOf ss) ≡ note m → n ≡ m
-- -- head-is (hold d) m x                        = just-injective x
-- -- head-is (rest d) m x                        = just-injective x
-- -- head-is (go↑ d size) m x                    = just-injective x
-- -- head-is (go↓ d size) m x                    = just-injective x
-- -- head-is (rearticulate d₁ d₂ x₁ ss ss₁) m x  = {! !}
-- -- head-is (ss ∘ ss₁) m x                      = {! !}
-- -- head-is (neighbor d₁ d₂ x₁ x₂ ss ss₁) m x   = {! !}
-- -- head-is (arpeggiate d₁ d₂ x₁ x₂ ss ss₁) m x = {! !}
-- -- head-is (motion↑ size d x₁) m x             = {! !}
-- -- head-is (motion↓ size d x₁) m x             = {! !}

-- -- last-is : ∀ {x} → (ss : StructuredSong x (n , t₁)) → (m : Note) → last (notesOf ss) ≡ note m → n ≡ m
-- -- last-is (hold d) m x                        = just-injective x
-- -- last-is (rest d) m x                        = just-injective x
-- -- last-is (go↑ d size) m x                    = just-injective x
-- -- last-is (go↓ d size) m x                    = just-injective x
-- -- last-is (rearticulate d₁ d₂ x₁ ss ss₁) m x  = {! !}
-- -- last-is (ss ∘ ss₁) m x                      = {! !}
-- -- last-is (neighbor d₁ d₂ x₁ x₂ ss ss₁) m x   = {! !}
-- -- last-is (arpeggiate d₁ d₂ x₁ x₂ ss ss₁) m x = {! !}
-- -- last-is (motion↑ size d x₁) m x             = {! !}
-- -- last-is (motion↓ size d x₁) m x             = {! !}

-- -- connected
-- --   : ∀ {x y}
-- --   → (ss₁ : StructuredSong x (n₁ , t₁))
-- --   → (ss₂ : StructuredSong (n₂ , t₂) y)
-- --   → Relationship n₁ n₂
-- --   → Connected Relationship (last (notesOf ss₁))
-- --                            (head (notesOf ss₂))
-- -- connected ss₁ ss₂ x
-- --   with last (notesOf ss₁) in eq₁
-- --      | head (notesOf ss₂) in eq₂
-- -- ... | note a | note b rewrite last-is ss₁ a eq₁ | head-is ss₂ b eq₂ = just x
-- -- ... | note a | rest   = just-nothing
-- -- ... | rest | note b   = nothing-just
-- -- ... | rest | rest     = nothing

-- -- -- related : ∀ {x y} → (song : StructuredSong x y) → Linked Relationship (Data.List.map proj₁ (unparse song))
-- -- -- related (hold d) = [-]
-- -- -- related (rest d) = [-]
-- -- -- related (go↑ d size) = [-]
-- -- -- related (go↓ d size) = [-]
-- -- -- related (rearticulate d₁ d₂ d≤d song song₁) with related song | related song₁
-- -- -- ... | r1 | r2 = subst (Linked Relationship) (sym (map-++-commute proj₁ (unparse song) (unparse song₁))) (++⁺ r1 (connected song song₁ rearticulation) r2)
-- -- -- related (song ∘ song₁) = {! !}
-- -- -- related (neighbor d₁ d₂ x x₁ song song₁) = {! !}
-- -- -- related (arpeggiate d₁ d₂ x x₁ song song₁) = {! !}
-- -- -- related (motion↑ size d x) = {! !}
-- -- -- related (motion↓ size d x) = {! !}





-- -- -- -- _ : unparse basic-step ≡ (note base , 2) ▹ (note base , 1) ▹ (note base , 0) ▹ (note (step base) , 3) ▹ (note (step (step base)) , 3) ▹ (note (step (step (step base))) , 3) ▹ (note (step (step (step (step base)))) , 3) ▹ fin
-- -- -- -- _ = refl

