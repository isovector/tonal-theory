module Musikal.Domain where

open import Musikal.Base
open import Interval using (Quality; p8) renaming (Interval to Int)
open Int
open import Pitch
open Quality
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Relation.Nullary

private variable
  𝔸 : Set

open import Data.List using (List; []; _∷_; foldr; _∷ʳ_)

data Strength : Set where
  strong medium weak : Strength

data Beat : Set where
  down up back 3rd : Beat

data SATB : Set where
  soprano alto tenor bass : SATB

triad : Quality → List (Music Int)
triad minor = 𝅘𝅥 p1 1𝔻 ∷ 𝅘𝅥 M3 1𝔻 ∷ 𝅘𝅥 p5 1𝔻 ∷ []
triad major = 𝅘𝅥 p1 1𝔻 ∷ 𝅘𝅥 m3 1𝔻 ∷ 𝅘𝅥 p5 1𝔻 ∷ []
triad perfect = 𝅘𝅥 p1 1𝔻 ∷ 𝅘𝅥 M3 1𝔻 ∷ 𝅘𝅥 p5 1𝔻 ∷ 𝅘𝅥 p8 1𝔻 ∷ []

par : Music 𝔸 → Music 𝔸 → Music 𝔸
par (𝄽 _) y = y
par x (𝄽 _) = x
par x y = x ∣ y

seq : Music 𝔸 → Music 𝔸 → Music 𝔸
seq l@(𝄽 x) y with x ≟ 0𝔻 
... | yes _ = y
... | no _ = l ▹ y
seq x r@(𝄽 y) with y ≟ 0𝔻 
... | yes _ = x
... | no _ = x ▹ r
seq x y = x ▹ y

chord : List (Music 𝔸) → Music 𝔸
chord = foldr par ⊘

arpeggiate : List (Music 𝔸) → Music 𝔸
arpeggiate = foldr _▹_ ⊘

transpose : Int → Music Pitch → Music Pitch
transpose i = map (i aboveᵖ_)

𝄆_𝄇 : Music 𝔸 → Music 𝔸
𝄆 m 𝄇 = m ▹ m

invertⁱ : List (Music Int) → List (Music Int)
invertⁱ [] = []
invertⁱ (i ∷ is) = is ∷ʳ map 8va i


etude17 : Music Pitch
etude17 = (rep ∣ hirep) ▹ transpose p8 (rep ∣ hirep)
  where
    rep = map (_aboveᵖ toNote E 2) 𝄆 𝄆 chord (triad minor) ▹ chord (triad major) 𝄇 𝄇
    hirep = delay (1𝔻 / 2𝔻) (transpose p8 rep)

4:4-beat : Music (Beat × Strength)
4:4-beat = 𝅘𝅥 (down , strong) q
         ▹ 𝅘𝅥 (back , weak)   q
         ▹ 𝅘𝅥 (3rd  , medium) q
         ▹ 𝅘𝅥 (back , weak)   q
  where
    q = 1𝔻 / 4𝔻

sec6 : Music Pitch
sec6 = lhs ∣ rhs
  where
    lhs = do
      4:4-beat
      map (_aboveᵖ toNote A♭ 2) (chord (Data.List.take 2 (triad major))) ▹ 𝅘𝅥 (toNote F 2) 1𝔻

    rhs = do
      4:4-beat
      i <- arpeggiate (triad perfect)
      pure (i aboveᵖ toNote F 4)



