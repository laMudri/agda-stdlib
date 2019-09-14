------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative semirings of elements to semimodules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.CommutativeSemiring {c ℓ} (elemCommutativeSemiring : CommutativeSemiring c ℓ) where

open import Algebra.Module
open import Algebra.Module.Properties
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.Semimodule as MkSemimodule

private
  module Prev = MkSemimodule elemCommutativeSemiring (self-semimodule elemCommutativeSemiring)

module _ {n : ℕ} where

  semimodule : Semimodule elemCommutativeSemiring c ℓ
  semimodule = Prev.semimodule {n = n}

