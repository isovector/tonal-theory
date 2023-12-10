module Inductive where

open import Data.Nat
open import Data.Nat.Properties
open Data.Nat renaming (ℕ to Pitch)
open import Relation.Binary.PropositionalEquality


lemma : ∀ x y w z → x ≡ w → (x + y ⊔ (w + z)) ≡ (x ⊔ w + (y ⊔ z))
lemma x y .x z refl = begin
  (x + y) ⊔ (x + z)  ≡⟨ sym (+-distribˡ-⊔ x y z) ⟩
  x + (y ⊔ z)        ≡⟨ cong (_+ _) (sym (⊔-idem x)) ⟩
  (x ⊔ x) + (y ⊔ z)  ∎
  where open ≡-Reasoning


postulate
  lemma₂ : ∀ m n d → m ≡ (n + d) → (m ⊔ n) ≡ (m ⊔ (n + d))

infixr 5 _∣_
infixr 6 _▹_

private variable
  x y : ℕ

data Music : Set where
  note : Pitch → ℕ → Music
  𝄽 : ℕ → Music
  _▹_ : Music → Music → Music
  _∣_ : Music → Music → Music


dur : Music → ℕ
dur (note x d) = d
dur (𝄽 d) = d
dur (x ▹ y) = dur x + dur y
dur (x ∣ y) = dur x ⊔ dur y

⊘ : Music
⊘ = 𝄽 0

postulate
  𝄽-hom  : ∀ x y
         → (𝄽 x) ▹ (𝄽 y)
         ≡ 𝄽(x + y)

  ▹-unitˡ : ∀ m
          → ⊘ ▹ m
          ≡ m
  ▹-unitʳ : ∀ m
          → m ▹ ⊘
          ≡ m
  ▹-assoc : ∀ x y z
          → x ▹ (y ▹ z)
          ≡ (x ▹ y) ▹ z

  ∣-unitʳ : ∀ m
          → m ∣ 𝄽 (dur m)
          ≡ m
  ∣-assoc : ∀ x y z
          → x ∣ (y ∣ z)
          ≡ (x ∣ y) ∣ z
  ∣-comm  : ∀ m n
          → m ∣ n
          ≡ n ∣ m
  ∣-idem  : ∀ m
          → m ∣ m
          ≡ m

  interchange
          : ∀ m₁ m₂ n₁ n₂
          → dur m₁ ≡ dur n₁
          → (m₁ ▹ m₂) ∣ (n₁ ▹ n₂)
          ≡ (m₁ ∣ n₁) ▹ (m₂ ∣ n₂)
  wait    : ∀ m n d
          → dur m ≡ dur n + d
          → m ∣ n
          ≡ m ∣ (n ▹ 𝄽 d)


open import Data.Product

splitIntoLines : ∀ m → ∃₂ λ x y → m ≡ x ∣ y
splitIntoLines n@(note p d) = n , 𝄽 d , sym (∣-unitʳ n)
splitIntoLines n@(𝄽 x)      = n , n   , sym (∣-idem n)
splitIntoLines (m ▹ n)
  with splitIntoLines n
... | n₁ , n₂ , refl
    = m ▹ n₁
    , m ▹ n₂
    , sym (trans (interchange m n₁ m n₂ refl)
                 (cong (_▹ _) (∣-idem m)))
splitIntoLines (m ∣ n) = m , n , refl

open import Data.Empty
open import Relation.Nullary

notSequential : ¬ (∀ m → ∃₂ λ x y → m ≡ (x ▹ y))
notSequential f with f (note 1 1 ∣ note 2 2)
... | x , y , ()

