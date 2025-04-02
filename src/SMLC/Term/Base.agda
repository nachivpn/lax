{-# OPTIONS --safe --without-K #-}

import Type
module SMLC.Term.Base (𝕤 : Type.Ty) where

open import Type public
import Context Ty as Context
import Substitution as Substitution

open Context public

data Tm : Ctx → Ty → Set where

  var  : (v : Var Γ a)
       ---------------
       → Tm Γ a

  lam  : (t : Tm (Γ `, a) b)
         -------------------
       → Tm Γ (a ⇒ b)

  app  : (t : Tm Γ (a ⇒ b))
       → (u : Tm Γ a)
         ------------------
       → Tm Γ b

  return : (t : Tm Γ a)
           ------------
         → Tm Γ (𝕞 a)
  
  letin : (t : Tm Γ (𝕞 a))
        → (u : Tm (Γ `, a) (𝕞 b))
          -----------------------
        → Tm Γ (𝕞 b)

  get   : (t : Tm (Γ `, 𝕤) (𝕞 a))
          -----------------------
        → Tm Γ (𝕞 a)

  put   : (t : Tm Γ 𝕤)
        → (u : Tm Γ (𝕞 a))
          -----------------------
        → Tm Γ (𝕞 a)

variable
  t t' t'' t''' : Tm Γ a
  u u' u'' u''' : Tm Γ a

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)     = var (wkVar w x)
wkTm w (lam t)     = lam (wkTm (keep w) t)
wkTm w (app t u)   = app (wkTm w t) (wkTm w u)
wkTm w (return t)  = return (wkTm w t)
wkTm w (letin t u) = letin (wkTm w t) (wkTm (keep w) u)
wkTm w (get t)     = get (wkTm (keep w) t)
wkTm w (put t u)   = put (wkTm w t) (wkTm w u)

open Substitution Ty Tm var wkTm public
  renaming (module Composition to SubstitutionComposition)

substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s (var x)     = substVar s x
substTm s (lam t)     = lam (substTm (keeps s) t)
substTm s (app t u)   = app (substTm s t) (substTm s u)
substTm s (return t)  = return (substTm s t)
substTm s (letin t u) = letin (substTm s t) (substTm (keeps s) u)
substTm s (get t)     = get (substTm (keeps s) t)
substTm s (put t u)   = put (substTm s t) (substTm s u)

open SubstitutionComposition substTm public
