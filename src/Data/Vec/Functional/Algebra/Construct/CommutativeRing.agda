------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative rings of elements to modules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.CommutativeRing {c ℓ} (elemCommutativeRing : CommutativeRing c ℓ) where

open import Algebra.Module
import Algebra.Structures.Module as ModuleS
import Algebra.FunctionProperties as FP
import Algebra.FunctionProperties.Module.Left as LModProp
import Algebra.FunctionProperties.Module.Right as RModProp
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Ring as MkRing

private
  open module Elem = CommutativeRing elemCommutativeRing

open MkRing Elem.ring

module _ {n : ℕ} where

  open ModuleS (_≈̇_ {n = n})

  isModule : IsModule elemCommutativeRing _+̇_ scaleₗ 0̇ -̇_
  isModule = record { isLeftModule = isLeftModule }

  module′ : Module elemCommutativeRing c ℓ
  module′ = record { isModule = isModule }

