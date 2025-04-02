{-# OPTIONS --safe --without-K #-}

import Type as Type
module SMLC.Term.NormalForm (𝕤 : Type.Ty) where

open import SMLC.Term.NormalForm.Base 𝕤 public 
open import SMLC.Term.NormalForm.Properties 𝕤 public
