------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative semirings of elements to semimodules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.CommutativeSemiring
  {c ℓ} (commutativeSemiring : CommutativeSemiring c ℓ)
  where

import Data.Vec.Functional.Algebra.Construct.CommutativeSemiring as MkCommutativeSemiring
import Data.Vec.Functional.Algebra.Construct.Semimodule as MkSemimodule

private
  module Vec = MkCommutativeSemiring commutativeSemiring
  module Mat {n} = MkSemimodule commutativeSemiring (Vec.semimodule {n})

open Mat public

