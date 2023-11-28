module GoalDirected where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties using (_≤?_)
open import Relation.Binary using (Rel; Tri)
open import Agda.Primitive using (lzero)
open import Relation.Nullary
open import Data.List.Relation.Unary.Linked
open import Data.List.Membership.Propositional renaming (_∈_ to is-in)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum

Pitch : Set
Pitch = ℕ

Time : Set
Time = ℕ

Duration : Set
Duration = ℕ

record Note : Set where
  constructor note
  field
    pitch    : Pitch
    time     : Time
    duration : Duration

postulate
  NoteOfSong : Note → Set
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
    → Consecutive (note p₁ t₁ d₁) (note p₂ d₂ d₂)

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

module _ {l : Line} {n₁ n₂ : Note} (n₁-in : n₁ ∈ l) (n₂-in : n₂ ∈ l) where
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

dropUntil : Time → (l : List Note) → Linked Consecutive l → Line
dropUntil t₀ [] [] = [] , []
dropUntil t₀ (note p t d ∷ .[]) [-]
  with t₀ ≤? t
... | yes t₀≤t = note p t d ∷ [] , [-]
... | no ¬t₀≤t = [] , []
dropUntil t₀ (note p t d ∷ x ∷ xs) (rel ∷ rels)
  with t₀ ≤? t
... | yes t₀≤t = note p t d ∷ x ∷ xs , rel ∷ rels
... | no ¬t₀≤t = dropUntil t₀ (x ∷ xs) rels

statusOf : note p t d ∈ l → (tₑ : Time) → t ≤ tₑ → Status
statusOf {n} {t₀} {d} {l} n∈l tₑ t₀≤tₑ = ?
