{-# OPTIONS --safe --without-K #-}

import Type as Type
module SMLC.Term.NormalForm.Properties (𝕤 : Type.Ty) where

open import SMLC.Term.Base 𝕤
open import SMLC.Term.NormalForm.Base 𝕤

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; subst₂ ; cong ; cong₂ ; module ≡-Reasoning)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl

------------------------
-- Naturality conditions
------------------------

-- Normal forms and neutrals obey "naturality" of embeddding, i.e.,
-- weakening can be commuted with embedding.

-- the mutual brothers normal forms and neutrals who,
-- as always, must be handled (mutually) together
embNe-nat  : (w : Γ ⊆ Γ') (n : Ne Γ a)
  → wkTm w (embNe-fun n) ≡ embNe-fun (wkNe w n)
embNf-nat  : (w : Γ ⊆ Γ') (n : Nf Γ a)
  → wkTm w (embNf-fun n) ≡ embNf-fun (wkNf w n)
embSNf-nat : (w : Γ ⊆ Γ') (n : SNf Γ a)
  → wkTm w (embSNf-fun n) ≡ embSNf-fun (wkSNf w n)

embNf-nat w (up  n) = embNe-nat w n
embNf-nat w (lam n) = cong lam (embNf-nat (keep w) n)
embNf-nat w (get m) = cong get (embSNf-nat (keep w) m)

embSNf-nat w (putret m n)    = cong₂ put (embNf-nat w m) (cong return (embNf-nat w n))
embSNf-nat w (putlet m n m') = cong₂ put (embNf-nat w m)
  (cong₂ letin (embNe-nat w n) (embNf-nat (keep w) m'))

embNe-nat w (var   v)   = refl
embNe-nat w (app   n m) = cong₂ app   (embNe-nat w n) (embNf-nat w m)

wkNe-pres-⊆-refl  : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
wkNf-pres-⊆-refl  : (n : Nf Γ a) → wkNf ⊆-refl n ≡ n
wkSNf-pres-⊆-refl : (n : SNf Γ a) → wkSNf ⊆-refl n ≡ n

wkNe-pres-⊆-refl (var   v)   = cong var (wkVar-pres-⊆-refl v)
wkNe-pres-⊆-refl (app   n m) = cong₂ app (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)

wkNf-pres-⊆-refl (up  n) = cong up  (wkNe-pres-⊆-refl n)
wkNf-pres-⊆-refl (lam n) = cong lam (wkNf-pres-⊆-refl n)
wkNf-pres-⊆-refl (get m) = cong get (wkSNf-pres-⊆-refl m)

wkSNf-pres-⊆-refl (putret m n)    = cong₂ putret (wkNf-pres-⊆-refl m) (wkNf-pres-⊆-refl n) 
wkSNf-pres-⊆-refl (putlet m n m') = cong₃ putlet (wkNf-pres-⊆-refl m)
  (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m')

wkNe-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe (w ∙ w') n ≡ wkNe w' (wkNe w n)
wkNf-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf (w ∙ w') n ≡ wkNf w' (wkNf w n)
wkSNf-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : SNf Γ a)
  → wkSNf (w ∙ w') n ≡ wkSNf w' (wkSNf w n)

wkNe-pres-⊆-trans w w' (var v)   = cong var (wkVar-pres-⊆-trans w w' v)
wkNe-pres-⊆-trans w w' (app n m) = cong₂ app (wkNe-pres-⊆-trans  w w' n) (wkNf-pres-⊆-trans w w' m)

wkNf-pres-⊆-trans w w' (up  n) = cong up  (wkNe-pres-⊆-trans w w' n)
wkNf-pres-⊆-trans w w' (lam n) = cong lam (wkNf-pres-⊆-trans (keep  w) (keep  w') n)
wkNf-pres-⊆-trans w w' (get m) = cong get (wkSNf-pres-⊆-trans (keep  w) (keep  w') m)

wkSNf-pres-⊆-trans w w' (putret m n)    = cong₂ putret (wkNf-pres-⊆-trans w w' m) (wkNf-pres-⊆-trans w w' n)
wkSNf-pres-⊆-trans w w' (putlet m n m') = cong₃ putlet (wkNf-pres-⊆-trans w w' m)
  (wkNe-pres-⊆-trans w w' n) (wkNf-pres-⊆-trans (keep w) (keep w') m')
