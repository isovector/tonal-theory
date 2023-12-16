module Engraving where

open import Data.Nat using (zero; suc)
open import Data.Product hiding (map)
open import Pitch
open import Data.String
  hiding (intersperse)
open import Data.List
  renaming (_++_ to _++ˡ_)
  hiding (replicate; [_])
open import Data.Sum hiding (map)
open import Data.Rational.Show renaming (show to showRat)
open import Musikal.Base
open import Musikal.Domain

engraveDuration : 𝔻 → String
engraveDuration (mkDur d _) = showRat d
-- engraveDuration 𝅝． = "1."
-- engraveDuration 𝅝   = "1"
-- engraveDuration 𝅗𝅥． = "2."
-- engraveDuration 𝅗𝅥   = "2"
-- engraveDuration 𝅘𝅥． = "4."
-- engraveDuration 𝅘𝅥   = "4"
-- engraveDuration 𝅘𝅥𝅮． = "8."
-- engraveDuration 𝅘𝅥𝅮   = "8"
-- engraveDuration 𝅘𝅥𝅯． = "16."
-- engraveDuration 𝅘𝅥𝅯   = "16"
-- engraveDuration 𝅘𝅥𝅰． = "32."
-- engraveDuration 𝅘𝅥𝅰   = "32"
-- -- engraveDuration (x ⁀ y) = engraveDuration x ++ "~ " ++ engraveDuration y
-- -- TODO(sandy): ERR OR
-- engraveDuration ⊘   = "128"

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

prettyPitchClass : PitchClass → String
prettyPitchClass A  = "A"
prettyPitchClass A♯ = "A♯"
prettyPitchClass B  = "B"
prettyPitchClass C  = "C"
prettyPitchClass C♯ = "C♯"
prettyPitchClass D  = "D"
prettyPitchClass D♯ = "D♯"
prettyPitchClass E  = "E"
prettyPitchClass F  = "F"
prettyPitchClass F♯ = "F♯"
prettyPitchClass G  = "G"
prettyPitchClass G♯ = "G♯"

prettyPitch : Pitch → String
prettyPitch p = prettyPitchClass (pitchClass p)

engraveText : String → String
engraveText msg = "\\markup { \n " ++ msg ++ " \n }"

open import Function using (case_of_; _∘_; id)

engravePitch : Pitch → String
engravePitch n with fromNote n
... | pc , o = engravePitchClass pc ++ (case o of λ
  { zero → ",,,"
  ; (suc zero) → ",,"
  ; (suc (suc zero)) → ","
  ; (suc (suc (suc n))) → replicate n '\'' })

engraveMusic : Music Pitch → String
engraveMusic (𝄽 d) = "r" ++ engraveDuration d
engraveMusic (𝅘𝅥 x d) = engravePitch x ++ engraveDuration d
engraveMusic (x ∣ y) = "\\partCombine { " ++ engraveMusic x ++ " } { " ++ engraveMusic y ++ " }"
engraveMusic (x ▹ y) = engraveMusic x ++ " " ++ engraveMusic y

preamble : String
preamble = "\n\\new Voice \\with {
  \\remove Note_heads_engraver
  \\consists Completion_heads_engraver
  \\remove Rest_engraver
  \\consists Completion_rest_engraver
}
\\absolute"

engraveVoice : Music Pitch → String
engraveVoice x = preamble ++ "{" ++ engraveMusic x ++ "}\n"


