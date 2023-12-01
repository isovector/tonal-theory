module Setwise.Base where

open import Data.Nat

Pitch : Set
Pitch = ℕ

Time : Set
Time = ℕ

Duration : Set
Duration = ℕ

record Note : Set where
  constructor note
  field
    pitch    : Pitch
    time     : Time
    duration : Duration

