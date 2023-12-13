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
  𝅘𝅥 : Pitch → ℕ → Music
  𝄽 : ℕ → Music
  _▹_ : Music → Music → Music
  _∣_ : Music → Music → Music


dur : Music → ℕ
dur (𝅘𝅥 x d) = d
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
          → (x ▹ y) ▹ z
          ≡ x ▹ (y ▹ z)

  ∣-unitʳ : ∀ m d
          → d ≤ dur m
          → m ∣ 𝄽 d
          ≡ m
  ∣-assoc : ∀ x y z
          → (x ∣ y) ∣ z
          ≡ x ∣ (y ∣ z)
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

∣-unitˡ : ∀ m d → d ≤ dur m → 𝄽 d ∣ m ≡ m
∣-unitˡ m d p = begin
  𝄽 d ∣ m  ≡⟨ ∣-comm _ _ ⟩
  m ∣ 𝄽 d  ≡⟨ ∣-unitʳ _ _ p ⟩
  m        ∎
  where open ≡-Reasoning

delay-by : ℕ → Music → Music
delay-by d = 𝄽 d ▹_

_▹→∣_ : Music → Music → Music
m ▹→∣ n = m ∣ delay-by (dur m) n

infixr 6 _▹→∣_

delayed-par : ∀ x y → x ▹ y ≡ x ▹→∣ y
delayed-par x y = begin
  x ▹ y                      ≡⟨ sym (cong (_▹ _) (∣-unitʳ x (dur x) ≤-refl)) ⟩
  (x ∣ 𝄽 (dur x)) ▹ y        ≡⟨ sym (cong (_ ▹_) (∣-unitˡ _ 0 z≤n)) ⟩
  (x ∣ 𝄽 (dur x)) ▹ (⊘ ∣ y)  ≡⟨ sym (interchange _ _ _ _ refl) ⟩
  x ▹ ⊘ ∣ 𝄽 (dur x) ▹ y      ≡⟨ cong (_∣ 𝄽 (dur x) ▹ y) (▹-unitʳ _) ⟩
  x ∣ 𝄽 (dur x) ▹ y          ∎
  where open ≡-Reasoning

data Seq (A : Music → Set) : Music → Set where
  embed : ∀ {m} → A m → Seq A m
  𝅘𝅥 : ∀ {p d} → Seq A (𝅘𝅥 p d)
  𝄽 : ∀ {d} → Seq A (𝄽 d)
  _▹_ : ∀ {x y} → Seq A x → Seq A y → Seq A (x ▹ y)

data Par (A : Music → Set) : Music → Set where
  embed : ∀ {m} → A m → Par A m
  𝅘𝅥 : ∀ {p d} → Par A (𝅘𝅥 p d)
  𝄽 : ∀ {d} → Par A (𝄽 d)
  _∣_ : ∀ {x y} → Par A x → Par A y → Par A (x ∣ y)

open import Data.Product
open import Data.Empty

ParSeq : Music → Set
ParSeq = Par (Seq (λ _ → ⊥))

SeqPar : Music → Set
SeqPar = Seq (Par (λ _ → ⊥))

elim-head : (a b c : Music) → a ▹ b ∣ a ▹ c ≡ a ▹ (b ∣ c)
elim-head a b c = begin
  a ▹ b ∣ a ▹ c      ≡⟨ interchange _ _ _ _ refl ⟩
  (a ∣ a) ▹ (b ∣ c)  ≡⟨ cong (_▹ _) (∣-idem _) ⟩
  a ▹ (b ∣ c)        ∎
  where open ≡-Reasoning

_▹→∣ₚ_ : ∀ {m n} → ParSeq m → ParSeq n → ParSeq (m ▹→∣ n)
m ▹→∣ₚ embed x = m ∣ embed (𝄽 ▹ x)
m ▹→∣ₚ 𝅘𝅥 = m ∣ embed (𝄽 ▹ 𝅘𝅥)
m ▹→∣ₚ 𝄽 = m ∣ embed (𝄽 ▹ 𝄽)
_▹→∣ₚ_ {mm} m (_∣_ {x} {y} n₁ n₂) with m ▹→∣ₚ n₁ | m ▹→∣ₚ n₂
... | a | b = subst ParSeq ( begin
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
                           ) (a ∣ b)
  where open ≡-Reasoning


asLines : (m : Music) → ParSeq m
asLines (𝅘𝅥 p d) = 𝅘𝅥
asLines (𝄽 d) = 𝄽
asLines (m ▹ n) = subst ParSeq (sym (delayed-par _ _)) (asLines m ▹→∣ₚ asLines n)
asLines (m ∣ n) = asLines m ∣ asLines n


open import Relation.Nullary

¬asChords : ¬ ((m : Music) → SeqPar m)
¬asChords f with f (𝅘𝅥 1 1 ▹ 𝅘𝅥 1 2 ∣ 𝅘𝅥 2 2 ▹ 𝅘𝅥 2 1)
... | embed (embed () ∣ _)

