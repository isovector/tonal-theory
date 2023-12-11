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

  toLine : List Atom → Music
  toLine = foldr concurrently ⊘

  concurrentLines : Music → List (List Atom) → Music
  concurrentLines m₀ =
    foldr (λ l m → toLine l ∣ m) m₀

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
    ≡⟨ cong (λ φ → foldr (λ l m → foldr concurrently ⊘ l ∣ m) φ ms) (∣-comm _ _) ⟩
      foldr (λ l m → foldr concurrently ⊘ l ∣ m) ((x ∣ n) ∣ foldr concurrently ⊘ m) ms
    ≡⟨ sym (lemma₃ (x ∣ n) ms _)  ⟩
      concurrentLines (x ∣ n) ms ∣ foldr concurrently ⊘ m
    ≡⟨ ∣-comm _ _  ⟩
      foldr concurrently ⊘ m ∣ concurrentLines (x ∣ n) ms
    ≡⟨⟩
      concurrentLines (x ∣ n) (m ∷ ms)
    ∎
    where open ≡-Reasoning

  open import Data.These using (These; this; that; these)

  aligning : ℕ → ℕ → List (List Atom) → List (List Atom) → List (List Atom)
  aligning dm dn = alignWith  (λ { (this x) → x ∷ʳ inj₂ dn ; (that x) → x ∷ʳ inj₂ dm ; (these x y) → x ++ y })

  open import Data.List.Relation.Unary.All

  lemma₄ : ∀ {dm dn} ml nl
         → All (λ l → dur (toLine l) ≡ dm) ml
         → All (λ l → dur (toLine l) ≡ dn) nl
         → concurrentLines ⊘ ml ▹ concurrentLines ⊘ nl ≡ concurrentLines ⊘ (aligning dm dn ml nl)
         × All (λ l → dur (toLine l) ≡ dm + dn) (aligning dm dn ml nl)
  lemma₄ {dm} {dn} [] nl x x₁ = {! !} , {! !}
  lemma₄ {dm} {dn} (ml ∷ ml₁) [] x x₁ = {! !}
  lemma₄ {dm} {dn} (ml ∷ ml₁) (nl ∷ nl₁) (px ∷ x) (px₁ ∷ x₁) = {! !}

  -- lemma₄ [] nl = trans (▹-unitˡ _) (cong (concurrentLines ⊘) (sym (map-id nl)))
  -- lemma₄ (m ∷ ms) [] =
  --   begin
  --     concurrentLines ⊘ (m ∷ ms) ▹ concurrentLines ⊘ []
  --   ≡⟨⟩
  --     (foldr concurrently (𝄽 0) m ∣ foldr (λ l → _∣_ (foldr concurrently (𝄽 0) l)) (𝄽 0) ms) ▹ 𝄽 0
  --   ≡⟨ ▹-unitʳ _ ⟩
  --     (foldr concurrently (𝄽 0) m ∣ foldr (λ l → _∣_ (foldr concurrently (𝄽 0) l)) (𝄽 0) ms)
  --   ≡⟨ cong (λ φ → (foldr concurrently (𝄽 0) m ∣ foldr (λ l → _∣_ (foldr concurrently (𝄽 0) l)) (𝄽 0) φ)) (sym (map-id ms)) ⟩
  --     foldr concurrently (𝄽 0) m ∣ foldr (λ l → _∣_ (foldr concurrently (𝄽 0) l)) (𝄽 0) (map (λ x → x) ms)
  --   ≡⟨⟩
  --     concurrentLines ⊘ (aligning (m ∷ ms) [])
  --   ∎
  --   where open ≡-Reasoning
  -- lemma₄ (m ∷ ms) (n ∷ ns) =
  --   begin
  --     concurrentLines ⊘ (m ∷ ms) ▹ concurrentLines ⊘ (n ∷ ns)
  --   ≡⟨⟩
  --     (foldr concurrently ⊘ m ∣ concurrentLines ⊘ ms) ▹ (foldr concurrently ⊘ n ∣ concurrentLines ⊘ ns)
  --   ≡⟨ ? ⟩
  --     foldr concurrently ⊘ (m ++ n) ∣ concurrentLines ⊘ (aligning ms ns)
  --   ≡⟨⟩
  --     concurrentLines ⊘ (aligning (m ∷ ms) (n ∷ ns))
  --   ∎
  --   where open ≡-Reasoning

  splitIntoLines : ∀ m → ∃₂ λ ls d → (m ≡ concurrentLines ⊘ ls) × All (λ l → dur (toLine l) ≡ d) ls
  splitIntoLines a@(note p d) = [ [ inj₁ (p , d) ] ] , d , sym (trans (∣-unitʳ (a ▹ ⊘) 0 z≤n) (▹-unitʳ a)) , +-identityʳ d ∷ []
  splitIntoLines a@(𝄽 d)      = [ [ inj₂      d  ] ] , d , sym (trans (∣-unitʳ (a ▹ ⊘) 0 z≤n) (▹-unitʳ a)) , +-identityʳ d ∷ []
  splitIntoLines (m ▹ n) with splitIntoLines m | splitIntoLines n
  ... | ml , md , refl , ma | nl , nd , refl , na = aligning md nd ml nl , md + nd , lemma₄ ml nl ma na
  splitIntoLines (m ∣ n) with splitIntoLines m | splitIntoLines n
  ... | ml , md , mp , ma | nl , nd , np , na = ml ++ nl , md ⊔ nd ,
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
    ∎) , ?
    where open ≡-Reasoning


  open import Data.Empty
  open import Relation.Nullary

  sequentialChords : List (List Atom) → Music
  sequentialChords =
    foldr (λ l m → foldr (λ { (inj₁ (p , d)) m → note p d ∣ m
                            ; (inj₂ d) m       → 𝄽 d      ∣ m
                            }) ⊘ l ▹ m) ⊘

  notSequential : ¬ (∀ m → ∃[ l ] m ≡ sequentialChords l)
  notSequential f with f (note 1 1 ∣ note 2 2)
  ... | [] , ()
  ... | x ∷ x₁ , ()

