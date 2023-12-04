open import Setwise.Base

module Setwise.Machinery (NoteOfSong : Note → Set) where

open import Data.List hiding (reverse; _∷ʳ_)
open import Data.Nat
open import Data.Nat.Properties using (_≤?_)
open import Relation.Binary using (Rel; Tri)
open import Agda.Primitive using (lzero)
open import Relation.Nullary
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Membership.Propositional renaming (_∈_ to is-in)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum

postulate
  IsStepInterval : Rel Pitch lzero
  IsSkipInterval : Rel Pitch lzero

private variable
  p p₁ p₂ p₃ p₄ : Pitch
  t t₁ t₂ t₃ t₄ : Time
  d d₁ d₂ d₃ d₄ : Duration
  n n₁ n₂ n₃ n₄ : Note

data Consecutive : Rel Note lzero where
  consecutive
    : NoteOfSong (note p₁ t₁ d₁)
    → NoteOfSong (note p₂ t₂ d₂)
    → t₁ + d₁ ≤ t₂
    → Consecutive (note p₁ t₁ d₁) (note p₂ t₂ d₂)

Line : Set
Line = Σ (List Note) (Linked Consecutive)

private variable
  l l₁ l₂ l₃ l₄ : Line
  lines : Line → Set

infix 10 _∈_

_∈_ : Note → Line → Set
n ∈ l = is-in n (proj₁ l)

record IsCounterpoint (SongLines : Line → Set) : Set where
  field
    total : NoteOfSong n
          → ∃[ line ]
                SongLines line
              × n ∈ line
    unique : ∀ {l₁ l₂}
           → SongLines l₁
           → SongLines l₂
           → n ∈ l₁
           → n ∈ l₂
           → l₁ ≡ l₂

module _ (l : Line) {n₁ n₂ : Note} (n₁-in : n₁ ∈ l) (n₂-in : n₂ ∈ l) where
  record IsRepetition : Set where
    field
      is-repetition : Note.pitch n₁ ≡ Note.pitch n₂

  record IsStep : Set where
    field
      is-step : IsStepInterval (Note.pitch n₁) (Note.pitch n₂)

  record IsSkip : Set where
    field
      is-skip : IsSkipInterval (Note.pitch n₁) (Note.pitch n₂)

  postulate
    categorize : Tri IsRepetition IsStep IsSkip


data Status : Set where
  confirmed rejected hanging : Status


data Resolves (l : Line) (n₁∈ : n₁ ∈ l) (n₂∈ : n₂ ∈ l) : Status → Set where
  confirms
    : Note.time n₁ < Note.time n₂
    → IsRepetition l n₁∈ n₂∈
    → Resolves l n₁∈ n₂∈ confirmed
  rejects
    : Note.time n₁ < Note.time n₂
    → IsStep l n₁∈ n₂∈
    → Resolves l n₁∈ n₂∈ rejected


record Resolution (l : Line) (n₁∈ : n₁ ∈ l) : Set where
  inductive
  field
    {resolving} : Note
    resolving∈ : resolving ∈ l
    status : Status
    resolution : Resolves l n₁∈ resolving∈ status
    unique
      : (n∈ : n ∈ l)
      → Note.time n₁ < Note.time n
      → Note.time n  < Note.time resolving
      → ¬ Σ Status (Resolves l n₁∈ n∈)


data Snoc {ℓ : _} (A : Set ℓ) : Set ℓ where
  []  : Snoc A
  _∷ʳ_ : Snoc A → A → Snoc A

infixl 5 _∷ʳ_

snocify : ∀ {ℓ} {A : Set ℓ} → List A → Snoc A
snocify {A = A} = go []
  where
    go : Snoc A → List A → Snoc A
    go acc [] = acc
    go acc (x ∷ xs) = go (acc ∷ʳ x) xs

test : List ℕ
test = 1 ∷ 2 ∷ 3 ∷ []

open import Data.Bool using (Bool; true; false; not)

isStep : Pitch → Pitch → Bool
isStep zero zero = true
isStep zero (suc zero) = true
isStep zero (suc (suc x₁)) = false
isStep (suc zero) zero = true
isStep (suc zero) (suc y) = isStep zero y
isStep (suc (suc x)) zero = false
isStep (suc (suc x)) (suc y) = isStep (suc x) y

open import Function using (_∘_)

removeSteps : Pitch → List Note → List Note
removeSteps x = boolFilter (not ∘ isStep x ∘ Note.pitch)

leftHanging : List Note → List Note
leftHanging = go ∘ snocify
  where
    go : Snoc Note → List Note
    go [] = []
    go (x ∷ʳ n) = n ∷ removeSteps (Note.pitch n) (go x)

