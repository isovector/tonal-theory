{-# OPTIONS --rewriting #-}

module Notes where

open import Pitch
open import Duration
open import Interval
open import Line
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (toℕ)



-- data Consonant : Rel Pitch lzero where
--   consonant↑ : {int : Interval} → ConsonantInterval int → Consonant p (int aboveᵖ p)
--   consonant↓ : {int : Interval} → ConsonantInterval int → Consonant (int aboveᵖ p) p

ode-chords : Line
ode-chords
  = stack (2 measures) (toNote E 4) m3
  ▹ stack (2 measures) (toNote C 4) p5
  ▹ note C4 𝅘𝅥
  -- ▹ stack (2 measures) (toNote E 4) m3
  -- ▹ stack (1 measures) (toNote C 4) M3
  -- ▹ note C4 (1 measures)


q : PitchClass → Line
q c = note (toNote c 4) 𝅘𝅥

h : PitchClass → Line
h c = note (toNote c 4) 𝅗𝅥

_>_ : PitchClass → Line → Line
c > l = q c ▹ l
infixr 5 _>_

D4 = toNote D 4
E4 = toNote E 4
F4 = toNote F 4
G4 = toNote G 4
A4 = toNote A 4
A5 = toNote A 5

ode : Line
ode = E > E > F > G > G > F > E > D > C > C > D > E > E > D > h D ▹ q E
    -- > E > F > G > G > F > E > D > C > C > D > E > D > C > h C


ode-ok : ode-chords ⇒ ode
ode-ok = begin
    stack (2 measures) E4 m3 ▹ stack (2 measures) C4 p5 ▹ note C4 𝅘𝅥
  ∼⟨ congˡ (arpeggiate₁ 𝅗𝅥． m3) ⟩
    (note E4 𝅗𝅥． ▹ note G4 (𝅘𝅥 ⁀ 𝅝)) ▹ stack (2 measures) C4 p5 ▹ note C4 𝅘𝅥
  ∼⟨ congˡ (congˡ (rearticulate 𝅘𝅥)) ⟩
    ((note E4 𝅘𝅥 ▹ note E4 𝅗𝅥) ▹ note G4 (𝅘𝅥 ⁀ 𝅝)) ▹ stack (2 measures) C4 p5 ▹ note C4 𝅘𝅥
  ∼⟨ congˡ assocʳ ⟩
    (note E4 𝅘𝅥 ▹ (note E4 𝅗𝅥 ▹ note G4 (𝅘𝅥 ⁀ 𝅝))) ▹ stack (2 measures) C4 p5 ▹ note C4 𝅘𝅥
  ∼⟨ congˡ (congʳ (step-motion↑ 𝅘𝅥 𝅘𝅥 m3 (C4 , ∈-diatonic M3 refl , ∈-diatonic p5 refl))) ⟩
                              -- WTF???
    (note E4 𝅘𝅥 ▹ (note E4 𝅘𝅥 ▹ note A5 𝅘𝅥 ▹ note G4 (𝅘𝅥 ⁀ 𝅝))) ▹ stack (2 measures) C4 p5 ▹ note C4 𝅘𝅥
  ∼⟨ ? ⟩
    E > E > F > G > G > F > E > D > C > C > D > E > E > D > h D ▹ q E
  ∎
  where open ⇒-Reasoning


-- _ : stack ((𝅘𝅥 ⁀ 𝅝) ⁀ 𝅘𝅥) (semitones 0) M6
--   ⇒ (note (semitones 0) 𝅘𝅥𝅮 ▹ note (semitones 0) 𝅘𝅥𝅮) ▹ note (semitones 2) 𝅘𝅥 ▹ note (semitones 4) 𝅘𝅥 ▹ note (semitones 5) 𝅘𝅥 ▹ note (semitones 7) 𝅘𝅥 ▹ note (semitones 9) 𝅘𝅥
-- _ =
--   begin
--     stack ((𝅘𝅥 ⁀ 𝅝) ⁀ 𝅘𝅥) A0 M6
--   ∼⟨ arpeggiate₁ {i = M6} (𝅘𝅥 *ᵈ 5) ⟩
--     note A0 (𝅘𝅥 *ᵈ 5) ▹ note (M6 aboveᵖ A0) 𝅘𝅥
--   ∼⟨ step-motion↑ 𝅘𝅥 𝅘𝅥 M6 (A0 , ∈-diatonic p1 refl , ∈-diatonic M6 refl) ⟩
--     note A0 𝅘𝅥 ▹ (note (semitones 2) 𝅘𝅥 ▹ note (semitones 4) 𝅘𝅥 ▹ note (semitones 5) 𝅘𝅥 ▹ note (semitones 7) 𝅘𝅥 ▹ note (semitones 9) 𝅘𝅥)
--   ∼⟨ cong (rearticulate 𝅘𝅥𝅮) refl ⟩
--     (note A0 𝅘𝅥𝅮 ▹ note A0 𝅘𝅥𝅮) ▹ note (semitones 2) 𝅘𝅥 ▹ note (semitones 4) 𝅘𝅥 ▹ note (semitones 5) 𝅘𝅥 ▹ note (semitones 7) 𝅘𝅥 ▹ note (semitones 9) 𝅘𝅥
--   ∎
--   where open ⇒-Reasoning
