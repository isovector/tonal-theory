module Setwise.Test where

open import Data.Nat
open import Setwise.Base
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.List.Relation.Unary.Linked as L hiding (zipWith)
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])

ode-pitches : List Pitch
ode-pitches = e ∷ e ∷ f ∷ g
            ∷ g ∷ f ∷ e ∷ d
            ∷ c ∷ c ∷ d ∷ e
            ∷ e ∷ d ∷ d ∷ []
  where
    c = 0
    d = 1
    e = 2
    f = 3
    g = 4

pitch-to-notes : List Pitch → List Note
pitch-to-notes ps = zipWith (λ p t → note p t 1) ps (upTo (length ps))

ode : List Note
ode = pitch-to-notes ode-pitches

open import Setwise.Machinery (_∈ ode)


ode-list : Line
ode-list = ode , consecutive (here refl) (there (here refl)) (s≤s z≤n)
               ∷ consecutive (there (here refl)) (there (there (here refl))) (s≤s (s≤s z≤n))
               ∷ consecutive (there (there (here refl))) (there (there (there (here refl)))) (s≤s (s≤s (s≤s z≤n)))
               ∷ consecutive (there (there (there (here refl)))) (there (there (there (there (here refl))))) (s≤s (s≤s (s≤s (s≤s z≤n))))
               ∷ consecutive (there (there (there (there (here refl))))) (there (there (there (there (there (here refl)))))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
               ∷ consecutive (there (there (there (there (there (here refl)))))) (there (there (there (there (there (there (here refl))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
               ∷ consecutive (there (there (there (there (there (there (here refl))))))) (there (there (there (there (there (there (there (here refl)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
               ∷ consecutive (there (there (there (there (there (there (there (here refl)))))))) (there (there (there (there (there (there (there (there (here refl))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
               ∷ consecutive (there (there (there (there (there (there (there (there (here refl))))))))) (there (there (there (there (there (there (there (there (there (here refl)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
               ∷ consecutive (there (there (there (there (there (there (there (there (there (here refl)))))))))) (there (there (there (there (there (there (there (there (there (there (here refl))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
               ∷ consecutive (there (there (there (there (there (there (there (there (there (there (here refl))))))))))) (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))
               ∷ consecutive (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))) (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))
               ∷ consecutive (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))) (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))
               ∷ consecutive (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))) (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))
               ∷ [-]

ode-is-counterpoint : IsCounterpoint (_≡ ode-list)
IsCounterpoint.total ode-is-counterpoint x = ode-list , refl , x
IsCounterpoint.unique ode-is-counterpoint refl refl x₂ x₃ = refl

