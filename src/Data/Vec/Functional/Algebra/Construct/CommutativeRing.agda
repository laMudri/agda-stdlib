------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative rings of elements to modules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.CommutativeRing {c ℓ} (elemCommutativeRing : CommutativeRing c ℓ) where

open import Algebra.Module
open import Algebra.Module.Properties
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.Module as MkModule

private
  module Prev = MkModule elemCommutativeRing (self-module elemCommutativeRing)

module _ {n : ℕ} where

  module′ : Module elemCommutativeRing c ℓ
  module′ = Prev.module′ {n = n}

