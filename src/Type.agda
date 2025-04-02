{-# OPTIONS --safe --without-K #-}
module Type where

infixr 7 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : (a : Ty) → (b : Ty) → Ty
  𝕞_  : (a : Ty) → Ty

variable
  a b c d : Ty
