module Inductive where

open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open Data.Nat renaming (ℕ to Pitch) hiding (_<_)
open import Relation.Binary.PropositionalEquality hiding ([_])


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

  ∣-unitʳ : ∀ m d
          → d ≤ dur m
          → m ∣ 𝄽 d
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


open import Data.Product hiding (map)

module _ where
  open import Data.List
  open import Data.List.Properties
  open import Data.Sum hiding (map)

  Atom : Set
  Atom = (Pitch × ℕ) ⊎ ℕ

  concurrently : Atom → Music → Music
  concurrently (inj₁ (p , d)) m = note p d ▹ m
  concurrently (inj₂ d)       m = 𝄽 d      ▹ m

  concurrentLines : Music → List (List Atom) → Music
  concurrentLines m₀ =
    foldr (λ l m → foldr concurrently ⊘ l ∣ m) m₀

  sequentialChords : List (List Atom) → Music
  sequentialChords =
    foldr (λ l m → foldr (λ { (inj₁ (p , d)) m → note p d ∣ m
                            ; (inj₂ d) m       → 𝄽 d      ∣ m
                            }) ⊘ l ▹ m) ⊘

  lemma₃ : ∀ x ml n → concurrentLines x ml ∣ n ≡ concurrentLines (x ∣ n) ml
  lemma₃ x [] n = refl
  lemma₃ x (m ∷ ms) n =
    begin
      concurrentLines x (m ∷ ms) ∣ n
    ≡⟨⟩
      (foldr concurrently ⊘ m ∣ concurrentLines x ms) ∣ n
    ≡⟨ sym (∣-assoc _ _ _) ⟩
      foldr concurrently ⊘ m ∣ (concurrentLines x ms ∣ n)
    ≡⟨ ∣-comm _ _ ⟩
      (concurrentLines x ms ∣ n) ∣ foldr concurrently ⊘ m
    ≡⟨ cong (_∣ _) (lemma₃ x ms n) ⟩
      concurrentLines (x ∣ n) ms ∣ foldr concurrently ⊘ m
    ≡⟨ lemma₃ (x ∣ n) ms (foldr concurrently ⊘ m) ⟩
      concurrentLines ((x ∣ n) ∣ foldr concurrently ⊘ m) ms
    ≡⟨ cong (λ φ → concurrentLines φ ms) (∣-comm _ _) ⟩
      concurrentLines (foldr concurrently ⊘ m ∣ (x ∣ n)) ms
    ≡⟨⟩
      foldr (λ l m → foldr concurrently (𝄽 0) l ∣ m) (foldr concurrently (𝄽 0) m ∣ x ∣ n) ms
    ≡⟨ cong (λ φ → foldr (λ l m → foldr concurrently (𝄽 0) l ∣ m) φ ms) (∣-comm _ _) ⟩
      foldr (λ l m → foldr concurrently (𝄽 0) l ∣ m) ((x ∣ n) ∣ foldr concurrently (𝄽 0) m) ms
    ≡⟨ sym (lemma₃ (x ∣ n) ms _)  ⟩
      concurrentLines (x ∣ n) ms ∣ foldr concurrently ⊘ m
    ≡⟨ ∣-comm _ _  ⟩
      foldr concurrently ⊘ m ∣ concurrentLines (x ∣ n) ms
    ≡⟨⟩
      concurrentLines (x ∣ n) (m ∷ ms)
    ∎
    where open ≡-Reasoning

  splitIntoLines : ∀ m → ∃[ l ] m ≡ concurrentLines ⊘ l
  splitIntoLines a@(note p d) = [ [ inj₁ (p , d) ] ] , sym (trans (∣-unitʳ (a ▹ ⊘) 0 z≤n) (▹-unitʳ a))
  splitIntoLines a@(𝄽 d)      = [ [ inj₂      d  ] ] , sym (trans (∣-unitʳ (a ▹ ⊘) 0 z≤n) (▹-unitʳ a))
  splitIntoLines (m ▹ n) with splitIntoLines m | splitIntoLines n
  ... | ml , mp | nl , np = {! !}
  splitIntoLines (m ∣ n) with splitIntoLines m | splitIntoLines n
  ... | ml , mp | nl , np = ml ++ nl ,
    (begin
      m ∣ n
    ≡⟨ cong (_∣ _) mp ⟩
      concurrentLines ⊘ ml ∣ n
    ≡⟨ lemma₃ ⊘ ml n ⟩
      concurrentLines (⊘ ∣ n) ml
    ≡⟨ cong (λ φ → concurrentLines φ ml) (trans (∣-comm ⊘ n) (∣-unitʳ n 0 z≤n)) ⟩
      concurrentLines n ml
    ≡⟨ cong (λ φ → foldr (λ l m → foldr concurrently ⊘ l ∣ m) φ ml) np ⟩
      concurrentLines (concurrentLines ⊘ nl) ml
    ≡⟨ sym (foldr-++ _ ⊘ ml nl) ⟩
      concurrentLines ⊘ (ml ++ nl)
    ∎)
    where open ≡-Reasoning


-- splitIntoLines n@(note p d) = ?
-- splitIntoLines n@(𝄽 x)      = n , n   , sym (∣-idem n)
-- splitIntoLines (m ▹ n)
--   with splitIntoLines n
-- ... | n₁ , n₂ , refl
--     = m ▹ n₁
--     , m ▹ n₂
--     , sym (trans (interchange m n₁ m n₂ refl)
--                  (cong (_▹ _) (∣-idem m)))
-- splitIntoLines (m ∣ n) = m , n , refl

open import Data.Empty
open import Relation.Nullary

notSequential : ¬ (∀ m → ∃₂ λ x y → m ≡ (x ▹ y))
notSequential f with f (note 1 1 ∣ note 2 2)
... | x , y , ()

