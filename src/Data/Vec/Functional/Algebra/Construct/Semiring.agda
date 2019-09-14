------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semirings of elements to left and right semimodules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Semiring {c ℓ} (elemSemiring : Semiring c ℓ) where

open import Algebra.Module
open import Algebra.Module.Properties
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.LeftSemimodule as MkLeftSemimodule
import Data.Vec.Functional.Algebra.Construct.RightSemimodule as MkRightSemimodule

private
  module Left = MkLeftSemimodule elemSemiring (self-leftSemimodule elemSemiring)
  module Right = MkRightSemimodule elemSemiring (self-rightSemimodule elemSemiring)

module _ {n : ℕ} where

  leftSemimodule : LeftSemimodule elemSemiring c ℓ
  leftSemimodule = Left.leftSemimodule {n = n}

  rightSemimodule : RightSemimodule elemSemiring c ℓ
  rightSemimodule = Right.rightSemimodule {n = n}

