{-# OPTIONS --rewriting #-}

module Categorical where

open import Agda.Builtin.Equality.Rewrite

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel; Transitive)
open import Algebra using (Op₂; Associative)
open import Relation.Binary.PropositionalEquality

open import Duration
open import Pitch

private variable
  t d₁ d₂ d₃ d₄ : Duration
  p p₁ p₂ : Pitch

infixl 5 _∙_

postulate
  -- Durations form a semigroup
  _∙_ : Op₂ Duration
  ∙-assoc : Associative _≡_ _∙_
{-# REWRITE ∙-assoc #-}


infix  2 _⇒_
infixr 5 _▹_
infix  1 _⊏_

postulate
  -- And we have a category of music
  _⇒_ : Rel Duration lzero
  id : t ⇒ t
  _▹_ : Transitive _⇒_

private variable
  f g h i : d₁ ⇒ d₂

postulate
  -- This thing is a category
  identityˡ : id ▹ f  ≡ f
  identityʳ : f  ▹ id ≡ f
  assoc : (f ▹ g) ▹ h ≡ f ▹ (g ▹ h)

  -- with simultaneity
  <_,_> : (f g : d₁ ⇒ d₂) → d₁ ⇒ d₂
  <,>-assoc : < < f , g > , h > ≡ < f , < g , h > >

  -- which distributes over ▹
  ▹-<,>-distrib : {f g : d₁ ⇒ d₂} {h i : d₂ ⇒ d₃} → < f , g > ▹ < h , i > ≡ < f ▹ h , g ▹ i >

  -- the whole thing is 2-category with refinement
  _⊏_ : Rel (d₁ ⇒ d₂) lzero
  same : f ⊏ f

private variable
  α β γ δ : f ⊏ g

{-# REWRITE assoc #-}

postulate

  -- horizontal composition
  _⨟_ : {f g : d₁ ⇒ d₂} → {h i : d₂ ⇒ d₃} → f ⊏ g → h ⊏ i → f ▹ h ⊏ g ▹ i
  ⨟-assoc : (α ⨟ β) ⨟ γ ≡ α ⨟ (β ⨟ γ)

  -- vertical composition
  _↓_ : Transitive (_⊏_ {d₁} {d₂})
  ↓-assoc : (α ↓ β) ↓ γ ≡ α ↓ (β ↓ γ)

  -- and a bonus temporal composition
  _∣_ : {f g h i : d₁ ⇒ d₂} → f ⊏ g → h ⊏ i → < f , h > ⊏ < g , i >
  -- ∣-assoc : (α ∣ β) ∣ γ ≡ α ∣ (β ∣ γ)

postulate
  -- with interchange:
  ↓⨟-interchange : (α ⨟ β) ↓ (γ ⨟ δ) ≡ (α ↓ γ) ⨟ (β ↓ δ)
  ↓∣-interchange : (α ∣ γ) ↓ (β ∣ δ) ≡ (α ↓ β) ∣ (γ ↓ δ)
  -- doesn't typecheck?
  -- ⨟∣-interchange : (α ∣ γ) ⨟ (β ∣ δ) ≡ (α ⨟ β) ∣ (γ ⨟ δ)

  -- and some primitives morphisms
  rest : (d : Duration) → t ⇒ t ∙ d
  note : (t : Duration) → (p : Pitch) → (d : Duration) → t ⇒ t ∙ d

  -- with some primitive 2 cells
  rearticulate : note t p (d₁  ∙                 d₂)
               ⊏ note t p  d₁  ▹ note (t ∙ d₁) p d₂

  arpeggiate : < note t p₁ (d₁ ∙ d₂) , note t p₂ (d₁ ∙ d₂) >
             ⊏   note t p₁ d₁        ▹ note (t ∙ d₁) p₂ d₂

  delay : note t p₁ d₁        ▹ note (t ∙ d₁) p₂ (d₂ ∙ d₃)
        ⊏ note t p₁ (d₁ ∙ d₂) ▹ note (t ∙ d₁ ∙ d₂) p₂ d₃


IsSimpleCounterpoint : t ⇒ t ∙ (𝅝 ∙ 𝅝) ∙ 𝅝 → Set
IsSimpleCounterpoint {t} refinement
  = < note t (toNote E 4) (𝅝 ∙ 𝅝)         ▹ note _ C4 𝅝
    , note t C4 𝅝 ▹ note _ (toNote G 4) 𝅝 ▹ note _ C4 𝅝 >
  ⊏ refinement

easy : t ⇒ t ∙ (𝅝 ∙ 𝅝) ∙ 𝅝
easy {t} = < note t (toNote E 4) 𝅝 ▹ note _ (toNote E 4) 𝅝 ▹ note _ C4 𝅝
           , note t C4 𝅝           ▹ note _ (toNote G 4) 𝅝 ▹ note _ C4 𝅝 >

easy-proof : IsSimpleCounterpoint {t} easy
easy-proof = (rearticulate ⨟ same) ∣ same


