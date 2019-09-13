------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative semirings of elements to semimodules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.CommutativeSemiring {c ℓ} (elemCommutativeSemiring : CommutativeSemiring c ℓ) where

open import Algebra.Module
import Algebra.Structures.Module as ModuleS
import Algebra.FunctionProperties.Module.Left as LModProp
import Algebra.FunctionProperties.Module.Right as RModProp
open import Data.Nat using (ℕ)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.CommutativeMonoid as MkCommutativeMonoid
import Data.Vec.Functional.Algebra.Construct.Semiring as MkSemiring

private
  open module Elem = CommutativeSemiring elemCommutativeSemiring

open MkSemiring Elem.semiring

module _ {n : ℕ} where

  open ModuleS (_≈̇_ {n = n})

  isSemimodule : IsSemimodule elemCommutativeSemiring _+̇_ scaleₗ 0̇
  isSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  semimodule : Semimodule elemCommutativeSemiring c ℓ
  semimodule = record { isSemimodule = isSemimodule }
