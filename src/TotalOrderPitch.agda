module TotalOrderPitch where

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel; Decidable; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (Injective)
open import Data.Product
open import Data.Nat
open import Data.Sum
open import Data.Maybe renaming (just to note; nothing to rest)

iterateN : {A : Set} → ℕ → A → (A → A) → A
iterateN zero    b f = b
iterateN (suc n) b f = f (iterateN n b f)

data Note : Set where
  base : Note
  step : Note → Note

data _≤ⁿ_ : Rel Note lzero where
  b≤n : ∀ {n} → base ≤ⁿ n
  s≤s : ∀ {m n} → m ≤ⁿ n → step m ≤ⁿ step n

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
  n n₁ n₂ : Note
  p p₁ p₂ : Pitch
  t d₁ d₂ : Duration

data IsNeighbor : Rel Note lzero where
  step↑ : IsNeighbor n (step n)
  step↓ : IsNeighbor (step n) n

data Direction : Set where
  ↑ ↓ : Direction

private variable
  dir : Direction

mutual
  data Motion (d : Duration) : Direction → ℕ → Note × Duration → Set where
    []  : Motion d dir 0 (n , t)
    _▹↑_ : {size : ℕ}
        → StructuredSong (n , t) (step n , t +ᵈ d)
        → Motion d ↑ size        (step n , t +ᵈ d)
        → Motion d ↑ (suc size)  (n , t)
    _▹↓_ : {size : ℕ}
        → StructuredSong (step n , t) (n , t +ᵈ d)
        → Motion d ↓ size             (n , t +ᵈ d)
        → Motion d ↓ (suc size)       (step n , t)

  data StructuredSong : Passage where
    hold  : (d : Duration) → StructuredSong (n , t)  (n , t +ᵈ d)
    rest  : (d : Duration) → StructuredSong (n , t)  (n , t +ᵈ d)
    step↑ : (d : Duration) → StructuredSong (n , t)  (step n , t +ᵈ d)
    step↓ : (d : Duration) → StructuredSong (step n , t)  (n , t +ᵈ d)
    rearticulation
      : (d₁ d₂ : Duration) → d₂ ≤ d₁
      → StructuredSong (n , t)       (n , t +ᵈ d₁)
      → StructuredSong (n , t +ᵈ d₁) (n , t +ᵈ d₁ +ᵈ d₂)
      → StructuredSong (n , t)       (n , t +ᵈ d₁ +ᵈ d₂)
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
      → Motion d ↑ size (n , t)
      → StructuredSong (n , t) (iterateN size n step , t +ᵈ (d *ᵈ size))
    motion↓
      : (size : ℕ)
      → (d : Duration)
      → Motion d ↓ size (iterateN size n step , t)
      → StructuredSong (iterateN size n step , t) (n , t +ᵈ (d *ᵈ size))

mutual
  unparseMotion : ∀ {d dir sz s} → Motion d dir sz s → Score
  unparseMotion [] = fin
  unparseMotion (x ▹↑ x₁) = unparse x ++ unparseMotion x₁
  unparseMotion (x ▹↓ x₁) = unparse x ++ unparseMotion x₁

  unparse : ∀ {n t y} → StructuredSong (n , t) y → Score
  unparse {n} (hold d) = (note n , d) ▹ fin
  unparse {n} (step↑ d) = (note n , d) ▹ fin
  unparse {n} (step↓ d) = (note n , d) ▹ fin
  unparse (rest d) = (rest , d) ▹ fin
  unparse (rearticulation d₁ d₂ x x₁ x₂) = unparse x₁ ++ unparse x₂
  unparse (neighbor d₁ d₂ x x₁ x₂ x₃)    = unparse x₂ ++ unparse x₃
  unparse (arpeggiate d₁ d₂ x x₁ x₂ x₃)  = unparse x₂ ++ unparse x₃
  unparse (motion↑ size d x) = unparseMotion x
  unparse (motion↓ size d x) = unparseMotion x

