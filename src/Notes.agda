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

D4 = toNote D 4
E4 = toNote E 4
F4 = toNote F 4
G4 = toNote G 4
A4 = toNote A 4
A5 = toNote A 5

ode-chords : Line
ode-chords
  = stack (2 measures) (toNote E 4) m3
  ▹ stack (2 measures) (toNote C 4) M3
  ▹ note E4 𝅘𝅥
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

ode-b1 : Line
ode-b1 = E > E > F > q G

ode-b2 : Line
ode-b2 = G > F > E > q D ▹ q C

ode-b3 : Line
ode-b3 = C > D > q E

ode-b4+ : Line
ode-b4+ = note E4 𝅘𝅥． ▹ note D4 𝅘𝅥𝅮 ▹ h D ▹ q E

ode : Line
ode = ode-b1 ▹▹ ode-b2 ▹▹ ode-b3 ▹▹ ode-b4+

ode-b4-ok : note E4 𝅝 ▹ note E4 𝅘𝅥 ⇒  ode-b4+
ode-b4-ok = begin
    note E4 𝅝 ▹ note E4 𝅘𝅥                              ∼⟨ neighbor 𝅘𝅥． D4 refl ⟩
    note E4 𝅘𝅥． ▹ note D4 (𝅘𝅥𝅮 ⁀         𝅗𝅥) ▹ note E4 𝅘𝅥  ∼⟨ congʳ (congˡ (rearticulate 𝅘𝅥𝅮 refl)) ⟩
    note E4 𝅘𝅥． ▹ (note D4 𝅘𝅥𝅮 ▹ note D4 𝅗𝅥) ▹ note E4 𝅘𝅥  ∼⟨ reassoc ⟩
    note E4 𝅘𝅥． ▹  note D4 𝅘𝅥𝅮 ▹ note D4 𝅗𝅥  ▹ note E4 𝅘𝅥  ∎
  where open ⇒-Reasoning

ode-b12-ok : stack (2 measures) E4 m3 ▹ note C4 𝅘𝅥 ⇒ ode-b1 ▹▹ ode-b2
ode-b12-ok = begin
  stack (𝅝 ⁀                                                        𝅝) E4 m3 ▹ note C4 𝅘𝅥   ∼⟨ congˡ (arpeggiate↑ 𝅗𝅥． m3 refl) ⟩
  (note E4 𝅗𝅥．                            ▹  note G4 (𝅘𝅥 ⁀           𝅝))      ▹ note C4 𝅘𝅥   ∼⟨ congˡ (step-motion↑ 𝅗𝅥 𝅘𝅥 m3 (C4 , ∈-diatonic M3 refl , ∈-diatonic p5 refl) refl) ⟩
  (note E4 𝅗𝅥                 ▹ note F4 𝅘𝅥  ▹  note G4 (𝅘𝅥 ⁀           𝅝))      ▹ note C4 𝅘𝅥   ∼⟨ congˡ (congˡ (rearticulate 𝅘𝅥 refl)) ⟩
  ((  note E4 𝅘𝅥 ▹ note E4 𝅘𝅥) ▹ note F4 𝅘𝅥  ▹  note G4 (𝅘𝅥 ⁀           𝅝))      ▹ note C4 𝅘𝅥   ∼⟨ congˡ assocˡ ⟩
  ((( note E4 𝅘𝅥 ▹ note E4 𝅘𝅥) ▹ note F4 𝅘𝅥) ▹  note G4 (𝅘𝅥 ⁀           𝅝))      ▹ note C4 𝅘𝅥   ∼⟨ congˡ (congʳ (rearticulate 𝅘𝅥 refl)) ⟩
  ((( note E4 𝅘𝅥 ▹ note E4 𝅘𝅥) ▹ note F4 𝅘𝅥) ▹ (note G4  𝅘𝅥  ▹  note G4 𝅝))      ▹ note C4 𝅘𝅥   ∼⟨ congˡ assocˡ ⟩
  ((((note E4 𝅘𝅥 ▹ note E4 𝅘𝅥) ▹ note F4 𝅘𝅥) ▹  note G4  𝅘𝅥) ▹  note G4 𝅝)       ▹ note C4 𝅘𝅥   ∼⟨ assocʳ ⟩
  ((( note E4 𝅘𝅥 ▹ note E4 𝅘𝅥) ▹ note F4 𝅘𝅥) ▹  note G4  𝅘𝅥) ▹ (note G4 𝅝        ▹ note C4 𝅘𝅥)  ∼⟨ congˡ reassoc ⟩
  ode-b1                                                 ▹ (note G4 𝅝        ▹ note C4 𝅘𝅥)  ∼⟨ congʳ (step-motion↓ 𝅘𝅥 𝅘𝅥 p5 (C4 , ∈-diatonic p1 refl , ∈-diatonic p5 refl) refl) ⟩
  ode-b1 ▹ (note G4 𝅘𝅥 ▹ note F4 𝅘𝅥 ▹ note E4 𝅘𝅥 ▹ note D4 𝅘𝅥 ▹ note C4 𝅘𝅥)                     ∼⟨ reassoc ⟩
  ode-b1 ▹▹ ode-b2                                                                         ∎
  where open ⇒-Reasoning

ode-ok : ode-chords ⇒ ode
ode-ok = begin
  let h = stack (2 measures) E4 m3 in
  h   ▹ stack (2 measures) C4 M3                                              ▹ note E4 𝅘𝅥   ∼⟨ congʳ (congˡ (arpeggiate↑ 𝅗𝅥． M3 refl)) ⟩
  h   ▹ ( note C4 𝅗𝅥．                           ▹  note E4 (𝅘𝅥  ⁀          𝅝)) ▹ note E4 𝅘𝅥   ∼⟨ congʳ (congˡ (congʳ (rearticulate 𝅘𝅥 refl))) ⟩
  h   ▹ ( note C4 𝅗𝅥．                           ▹ (note E4 𝅘𝅥   ▹  note E4 𝅝)) ▹ note E4 𝅘𝅥   ∼⟨ congʳ (congˡ assocˡ) ⟩
  h   ▹ ((note C4 𝅗𝅥．                           ▹  note E4 𝅘𝅥)  ▹  note E4 𝅝)  ▹ note E4 𝅘𝅥   ∼⟨ congʳ assocʳ ⟩
  h   ▹ ( note C4 𝅗𝅥．                           ▹  note E4 𝅘𝅥)  ▹ (note E4 𝅝   ▹ note E4 𝅘𝅥)  ∼⟨ congʳ (congʳ ode-b4-ok) ⟩
  h   ▹ ( note C4 𝅗𝅥．                           ▹  note E4 𝅘𝅥)  ▹ ode-b4+                    ∼⟨ congʳ (congˡ (step-motion↑ 𝅗𝅥 𝅘𝅥 M3 (C4 , ∈-diatonic p1 refl , ∈-diatonic M3 refl) refl)) ⟩
  h   ▹ ( note C4 𝅗𝅥                 ▹ note D4 𝅘𝅥 ▹  note E4 𝅘𝅥)  ▹ ode-b4+                    ∼⟨ congʳ (congˡ (congˡ (rearticulate 𝅘𝅥 refl))) ⟩
  h   ▹ ((note C4 𝅘𝅥  ▹   note C4 𝅘𝅥) ▹ note D4 𝅘𝅥 ▹  note E4 𝅘𝅥)  ▹ ode-b4+                    ∼⟨ assocˡ ⟩
  (h  ▹ ((note C4 𝅘𝅥  ▹   note C4 𝅘𝅥) ▹ note D4 𝅘𝅥 ▹  note E4 𝅘𝅥)) ▹ ode-b4+                    ∼⟨ congˡ reassoc ⟩
  (h  ▹   note C4 𝅘𝅥  ▹   note C4 𝅘𝅥  ▹ note D4 𝅘𝅥 ▹  note E4 𝅘𝅥)  ▹ ode-b4+                    ∼⟨ congˡ assocˡ ⟩
  ((h ▹   note C4 𝅘𝅥) ▹   note C4 𝅘𝅥  ▹ note D4 𝅘𝅥 ▹  note E4 𝅘𝅥)  ▹ ode-b4+                    ∼⟨ assocʳ ⟩
  (h  ▹   note C4 𝅘𝅥) ▹ ((note C4 𝅘𝅥  ▹ note D4 𝅘𝅥 ▹  note E4 𝅘𝅥)  ▹ ode-b4+)                   ∼⟨ congˡ ode-b12-ok ⟩
  (ode-b1 ▹▹ ode-b2) ▹ ((note C4 𝅘𝅥  ▹ note D4 𝅘𝅥 ▹  note E4 𝅘𝅥)  ▹ ode-b4+)                   ∼⟨ reassoc ⟩
  ode-b1 ▹▹ ode-b2 ▹▹ ode-b3 ▹▹ ode-b4+                                                     ∎
  where open ⇒-Reasoning

-- _ : complexity ode-ok ≡
-- _ = refl

