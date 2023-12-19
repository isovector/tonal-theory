module Denotation where

open import Duration
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Agda.Primitive

private variable
  ℓ : Level

Music : Set ℓ → Set ℓ
Music 𝔸 = (t : 𝔻) → 𝔸

private variable
  𝔸 𝔹 : Set

open import Algebra.Bundles

map : (𝔸 → 𝔹) → Music 𝔸 → Music 𝔹
map f m t = f (m t)

pure : 𝔸 → Music 𝔸
pure a _ = a

join : Music (Music 𝔸) → Music 𝔸
join m t = m t t

_>>=_ : Music 𝔸 → (𝔸 → Music 𝔹) → Music 𝔹
ma >>= f = join (map f ma)

_>>_ : Music 𝔸 → Music 𝔹 → Music 𝔹
ma >> mb = ma >>= λ _ → mb

_⊗_ : Music 𝔸 → Music 𝔹 → Music (𝔸 × 𝔹)
(m ⊗ n) t = m t , n t

module _ {c ℓ₁} ⦃ Mon : Monoid c ℓ₁ ⦄ where
  open Monoid Mon renaming (Carrier to X)

  𝅘𝅥 : X → 𝔻 → Music X
  𝅘𝅥 a d t with t ≤? d
  ... | yes _ = a
  ... | no  _ = ε

  _∣_ : Music X → Music X → Music X
  (m ∣ n) t = m t ∙ n t

  anticipate : 𝔻 → Music 𝔸 → Music 𝔸
  anticipate d m t = m (d + t)

  delay : 𝔻 → Music X → Music X
  delay d m t with d ≤? t
  ... | yes d≤t = m (sub t d d≤t)
  ... | no ¬d≤t = ε

  record Length (m : Music X) : Set c where
    field
      length : 𝔻
      all-ε : ∀ t → length ≤ t → m t ≡ ε
      least-such : ∀ tₑ → (∀ t → tₑ ≤ t → m t ≡ ε) → length ≤ tₑ

  postulate
    finite? : (m : Music X) → Dec (Length m)

  _▹_ : Music X → Music X → Music X
  m ▹ n with finite? m
  ... | no  _   = m
  ... | yes len = m ∣ delay (Length.length len) n

  {-# TERMINATING #-}
  forever : Music X → Music X
  forever m t with finite? m
  ... | no  _   = m t
  ... | yes len with Length.length len ≤? t
  ... | yes l≤t = forever m (sub t (Length.length len) l≤t)
  ... | no ¬l≤t = m t

