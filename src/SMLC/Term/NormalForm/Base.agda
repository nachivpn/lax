{-# OPTIONS --safe --without-K #-}

import Type
module SMLC.Term.NormalForm.Base (𝕤 : Type.Ty) where

open import SMLC.Term.Base 𝕤

---------------
-- Normal forms
---------------

data Ne  : Ctx → Ty → Set
data Nf  : Ctx → Ty → Set
data SNf : Ctx → Ty → Set

data Ne where
  var : Var Γ a → Ne Γ a
  app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b

data Nf where
  up  : Ne Γ ι → Nf Γ ι
  lam : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  get : SNf (Γ `, 𝕤) (𝕞 a) → Nf Γ (𝕞 a)

data SNf where
  putret : Nf Γ 𝕤 → Nf Γ a → SNf Γ (𝕞 a)
  putlet : Nf Γ 𝕤 → Ne Γ (𝕞 a) → Nf (Γ `, a) (𝕞 b) → SNf Γ (𝕞 b)

embNe-fun  : Ne Γ a  → Tm Γ a
embNf-fun  : Nf Γ a  → Tm Γ a
embSNf-fun : SNf Γ a → Tm Γ a

embNe-fun (var  x)   = var x
embNe-fun (app  m n) = app (embNe-fun m) (embNf-fun n)

embNf-fun (up  x)     = embNe-fun x
embNf-fun (lam n)     = lam (embNf-fun n)
embNf-fun (get m)     = get (embSNf-fun m)

embSNf-fun (putret m n)    = put (embNf-fun m) (return (embNf-fun n))
embSNf-fun (putlet m n m') = put (embNf-fun m) (letin (embNe-fun n) (embNf-fun m'))

wkNe  : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf  : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a
wkSNf : Γ ⊆ Γ' → SNf Γ a → SNf Γ' a

wkNe w (var x)     = var (wkVar w x)
wkNe w (app n m)   = app (wkNe w n) (wkNf w m)

wkNf w (up n)    = up (wkNe w n)
wkNf w (lam n)   = lam (wkNf (keep w) n)
wkNf w (get m)   = get (wkSNf (keep w) m)

wkSNf w (putret m n)    = putret (wkNf w m) (wkNf w n)
wkSNf w (putlet m n m') = putlet (wkNf w m) (wkNe w n) (wkNf (keep w) m')
