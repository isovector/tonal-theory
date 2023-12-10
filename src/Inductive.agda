-- {-# OPTIONS --cubical                     #-}
-- {-# OPTIONS --warning=noInteractionMetaBoundaries #-}

module Inductive where

open import Data.Nat
open import Data.Nat.Properties
open Data.Nat renaming (ℕ to Pitch)
-- open import Agda.Builtin.Cubical.Path
-- open import Agda.Primitive.Cubical
--   renaming (primTransp to transp; primINeg to ∼)
open import Relation.Binary.PropositionalEquality
  -- renaming (_≡_ to Eq; refl to same)

-- Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
-- Path A a b = PathP (λ _ → A) a b

-- refl : ∀ {ℓ} {A : Set ℓ} {x : A} → Path A x x
-- refl {x = x} = λ i → x

-- upgrade : ∀ {A : Set} {m n : A} → Eq m n → m ≡ n
-- upgrade same = refl

-- downgrade : ∀ {A : Set} {m n : A} → m ≡ n → Eq m n
-- downgrade {m = m} {n} x = transp (λ i → Eq m (x i)) i0 same


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

postulate
  𝄽-cont : ∀ x y → 𝄽 x ▹ 𝄽 y ≡ 𝄽 (x + y)
  ∣-unitʳ : ∀ m → m ∣ 𝄽 (dur m) ≡ m
  ∣-comm : ∀ m n → m ∣ n ≡ n ∣ m
  ∣-idem : ∀ m → m ∣ m ≡ m
  distrib : ∀ m₁ m₂ n₁ n₂ → dur m₁ ≡ dur n₁ → (m₁ ▹ m₂) ∣ (n₁ ▹ n₂) ≡ (m₁ ∣ n₁) ▹ (m₂ ∣ n₂)
  ▹-unitˡ : ∀ m → 𝄽 0 ▹ m ≡ m
  ▹-unitʳ : ∀ m → m ▹ 𝄽 0 ≡ m
  wait : ∀ m n d → dur m ≡ dur n + d → m ∣ n ≡ m ∣ (n ▹ 𝄽 d)

  -- dur (𝄽-cont x y i) = refl {x = x + y} i
  -- dur (∣-unitʳ m i) = upgrade (⊔-idem (dur m)) i
  -- dur (∣-idem m i) = upgrade (⊔-idem (dur m)) i
  -- dur (∣-comm m n i) = upgrade (⊔-comm (dur m) (dur n)) i
  -- dur (distrib m₁ m₂ n₁ n₂ eq i) = upgrade (lemma (dur m₁) (dur m₂) (dur n₁) (dur n₂) (downgrade eq)) i
  -- dur (▹-unitˡ m i) = upgrade (+-identityˡ (dur m)) i
  -- dur (▹-unitʳ m i) = upgrade (+-identityʳ (dur m)) i
  -- dur (wait m n d eq i) = upgrade (lemma₂ (dur m) (dur n) d (downgrade eq)) i

-- symi : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
-- symi eq i = eq (∼ i)


open import Data.Product

splitIntoLines : ∀ m → ∃₂ λ x y → m ≡ (x ∣ y)
splitIntoLines n@(note p d) = n , 𝄽 d , sym (∣-unitʳ n)
splitIntoLines n@(𝄽 x) = n , n , sym (∣-idem n)
splitIntoLines (m ▹ n)
  with splitIntoLines n
... | n₁ , n₂ , refl
    = m ▹ n₁
    , m ▹ n₂
    , sym (trans (distrib m n₁ m n₂ refl)
                 (cong (_▹ _) (∣-idem m)))
splitIntoLines (m ∣ n) = m , n , refl

open import Data.Empty
open import Relation.Nullary

notSequential : ¬ (∀ m → ∃₂ λ x y → m ≡ (x ▹ y))
notSequential f with f (note 1 1 ∣ note 2 2)
... | x , y , ()

