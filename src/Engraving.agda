{-# OPTIONS --rewriting #-}

module Engraving where

open import Data.Nat using (zero; suc)
open import Data.Product hiding (map)
open import Pitch
open import Duration
open import Line
open import Data.String
  hiding (intersperse)
open import Data.List
  renaming (_++_ to _++ˡ_)
  hiding (replicate)

engraveDuration : Duration → String
engraveDuration 𝅝． = "1."
engraveDuration 𝅝   = "1"
engraveDuration 𝅗𝅥． = "2."
engraveDuration 𝅗𝅥   = "2"
engraveDuration 𝅘𝅥． = "4."
engraveDuration 𝅘𝅥   = "4"
engraveDuration 𝅘𝅥𝅮． = "8."
engraveDuration 𝅘𝅥𝅮   = "8"
engraveDuration 𝅘𝅥𝅯． = "16."
engraveDuration 𝅘𝅥𝅯   = "16"
engraveDuration 𝅘𝅥𝅰． = "32."
engraveDuration 𝅘𝅥𝅰   = "32"
engraveDuration (x ⁀ y) = engraveDuration x ++ "~ " ++ engraveDuration y
-- TODO(sandy): ERR OR
engraveDuration ⊘   = "128"

engravePitchClass : PitchClass → String
engravePitchClass A  = "a"
engravePitchClass A♯ = "ais"
engravePitchClass B  = "b"
engravePitchClass C  = "c"
engravePitchClass C♯ = "cis"
engravePitchClass D  = "d"
engravePitchClass D♯ = "dis"
engravePitchClass E  = "e"
engravePitchClass F  = "f"
engravePitchClass F♯ = "fis"
engravePitchClass G  = "g"
engravePitchClass G♯ = "gis"

open import Function using (case_of_)

engravePitch : Pitch → String
engravePitch n with fromNote n
... | pc , o = engravePitchClass pc ++ (case o of λ
  { zero → ",,,"
  ; (suc zero) → ",,"
  ; (suc (suc zero)) → ","
  ; (suc (suc (suc n))) → replicate n '\'' })

engraveLine : Line → String
engraveLine (rest d) = "r" ++ engraveDuration d
engraveLine (note x d) = engravePitch x ++ engraveDuration d
engraveLine (stack d p {i} x) = "<" ++ engravePitch p ++ " " ++ engravePitch (i aboveᵖ p) ++ ">" ++ engraveDuration d
engraveLine (x ▹ y) = engraveLine x ++ " " ++ engraveLine y

preamble : String
preamble = "\n\\new Voice \\with {
  \\remove Note_heads_engraver
  \\consists Completion_heads_engraver
  \\remove Rest_engraver
  \\consists Completion_rest_engraver
}
\\absolute"

engraveVoice : Line → String
engraveVoice x = preamble ++ "{" ++ engraveLine x ++ "}\n"

engraveDerivation : ∀ {l₁ l₂} → l₁ ⇒ l₂ → List Line
engraveDerivation (trans x y) =
  engraveDerivation x ++ˡ engraveDerivation y
engraveDerivation {l₁} {l₃} (cong {a} {b} {c} {d} x y) =
  l₁ ∷ (map (_▹ c) (engraveDerivation x) ++ˡ map (b ▹_) (engraveDerivation y)) ∷ʳ l₃
engraveDerivation {l₁} {l₂} z = l₁ ∷ l₂ ∷ []

engrave : ∀ {l₁ l₂} → l₁ ⇒ l₂ → String
engrave d = unlines (derun _≟_ (map engraveVoice (engraveDerivation d)))
