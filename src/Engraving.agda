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
  hiding (replicate; [_])
open import Data.Sum hiding (map)

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

prettyDuration : Duration → String
prettyDuration (x ⁀ y) = prettyDuration x ++ " + " ++ prettyDuration y
prettyDuration d = "\\note {" ++ engraveDuration d ++ "} #UP"

open import Data.Maybe using (Maybe; just; nothing)

engraveReason : ∀ {l₁ l₂} → l₁ ⇒ l₂ → Maybe String
engraveReason {note p _} (rearticulate {d₂ = d₂} {d = d}  d₁ x) = just ("rearticulate " ++ prettyPitch p ++ " " ++ prettyDuration d ++ "  into  " ++ prettyDuration d₁ ++ " and " ++ prettyDuration d₂)
engraveReason {note p d ▹ _} (neighbor d₁ p₂ x) = just ("neighbor " ++ prettyPitch p₂ ++ " between " ++ prettyPitch p)
engraveReason {_} {note p d ▹ _} (arpeggiate↑ {i = i} d₁ ci x) = just ("arpeggiate chord upwards into " ++ prettyPitch p ++ " and " ++ prettyPitch (i aboveᵖ p))
engraveReason {_} {note p d ▹ _} (arpeggiate↓ {i = i} d₁ ci x) = just ("arpeggiate chord downwards into " ++ prettyPitch (i aboveᵖ p) ++ " and " ++ prettyPitch p)
engraveReason {note p _ ▹ _} (step-motion↑  d₁ d₂ {i = i} x (tonic , _) x₁) = just ("step motion in " ++ prettyPitch tonic ++ "M upwards from " ++ prettyPitch p ++ " to " ++ prettyPitch (i aboveᵖ p))
engraveReason {_ ▹ note p _} (step-motion↓ d₁ d₂ {i = i} x (tonic , _) x₁) = just ("step motion in " ++ prettyPitch tonic ++ "M downwards from " ++ prettyPitch (i aboveᵖ p) ++ " to " ++ prettyPitch p)
engraveReason delay-note = just "delay"
engraveReason delay-stack = just "delay"
engraveReason delay-rest = just "delay"
engraveReason refl = nothing
engraveReason _⇒_.assocʳ = nothing
engraveReason _⇒_.assocˡ = nothing
engraveReason (cong x x₁) = nothing
engraveReason (trans x x₁) = nothing


engraveDerivation : ∀ {l₁ l₂} → l₁ ⇒ l₂ → List (String ⊎ Line)
engraveDerivation (trans x y) =
  engraveDerivation x ++ˡ engraveDerivation y
engraveDerivation {l₁} {l₃} (cong {a} {b} {c} {d} x y) =
  inj₂ l₁ ∷ (map [ inj₁ , (inj₂ ∘ (_▹ c)) ] (engraveDerivation x) ++ˡ map [ inj₁ , (inj₂ ∘ (b ▹_)) ] (engraveDerivation y)) ∷ʳ inj₂ l₃
engraveDerivation {l₁} {l₂} z
  with engraveReason z
... | just reason = inj₂ l₁ ∷ inj₁ (engraveText reason) ∷ inj₂ l₂ ∷ []
... | nothing = inj₂ l₁ ∷ inj₂ l₂ ∷ []

engrave : ∀ {l₁ l₂} → l₁ ⇒ l₂ → String
engrave d = unlines (derun _≟_ (map [ id , engraveVoice ] (engraveDerivation d)))
