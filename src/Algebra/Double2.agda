------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Double2 where

open import Algebra
import Algebra.Structures.Double2 as Str
open import Algebra.FunctionProperties.Core
open import Algebra.FunctionProperties.Double.Core
open import Level
open import Relation.Binary

record Left_─Semimodule {r ℓr} (semiring : Semiring r ℓr) m ℓm
                        : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Semiring semiring

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isLeftSemimodule : IsLeft semiring ─Semimodule _+ᴹ_ _*ₗ_ 0ᴹ

  open IsLeft_─Semimodule isLeftSemimodule public

