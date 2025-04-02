{-# OPTIONS --safe --without-K #-}

import Type as Type
module SMLC.Term (𝕤 : Type.Ty) where

open import SMLC.Term.Base 𝕤 public
open import SMLC.Term.Properties 𝕤 public
