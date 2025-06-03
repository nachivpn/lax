{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.CFrame as CF
  
module Demo.Cover
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (𝒦   : KPsh)
  (let open KPsh 𝒦)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core 𝒦 _∈_)
  (CF : CFrame)
  where

open import Function using (id ; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂)
  
private
  variable
    w w' w'' u u' v v' : W

open CFrame CF

-- Upper set
record USet : Set₁ where
  constructor uset
  field
    Fam : W → Set
    wk  : w ⊆ w' → Fam w → Fam w'

open import Data.Sum

_⊎'_ : USet → USet → USet
(uset X wkX) ⊎' (uset Y wkY) = uset (λ w → X w ⊎ Y w) wk+
  where
  wk+ : w ⊆ w' → X w ⊎ Y w → X w' ⊎ Y w'
  wk+ i (inj₁ x) = inj₁ (wkX i x)
  wk+ i (inj₂ y) = inj₂ (wkY i y)

open USet renaming (Fam to _₀_) public

Cover' : USet → USet
Cover' A = uset CoverFam wkCov
  where
  CoverFam : W → Set
  CoverFam = λ w → Σ (K w) λ k → ForAllW k λ v → A ₀ v

  wkCov : w ⊆ w' → CoverFam w → CoverFam w' 
  wkCov i (k , f) = wkK i k , λ p → wk A (factor⊆ i k p) (f (factor∈ i k p))

record _→̇_ (X Y : USet) : Set where
  constructor fun
  field
    apply : ∀ {w} → X ₀ w → Y ₀ w

open _→̇_ public

id' : {A : USet} → A →̇ A
id' .apply = id

_∘'_ : {A B C : USet} → B →̇ C → A →̇ B → A →̇ C
(f ∘' g) .apply = f .apply ∘ g .apply

inj₁' : {A B : USet} → A →̇ (A ⊎' B)
inj₁' .apply = inj₁

inj₂' : {A B : USet} → B →̇ (A ⊎' B)
inj₂' .apply = inj₂

[_,_]' : {A B C : USet} →  A →̇ C → B →̇ C → (A ⊎' B) →̇  C
[ f , g ]' .apply = [ f .apply , g .apply ]

mapCover' : {A B : USet} → (f : A →̇ B) → Cover' A →̇ Cover' B
mapCover' f .apply (k , g) = k , f .apply ∘ g

module _ {A B : USet} (run : {w : W} (k : K w) (f : ForAllW k (A ₀_)) → B ₀ w) where

  runCover : Cover' A →̇ B
  runCover .apply (k , f) = run k f

module Pointed (Id : Identity CF) where
  open Identity Id

  return' : {A : USet} → A →̇ Cover' A
  return' {A} .apply {w} x = idK[ w ] , λ v → subst (A ₀_) (id∈ v) x
