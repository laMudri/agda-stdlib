------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semirings of elements to left and right semimodules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.Semiring {c ℓ} (semiring : Semiring c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Semiring as MkSemiring
import Data.Vec.Functional.Algebra.Construct.LeftSemimodule as MkLeftSemimodule
import Data.Vec.Functional.Algebra.Construct.RightSemimodule as MkRightSemimodule

private
  module Vec = MkSemiring semiring
  module MatL {n} = MkLeftSemimodule semiring (Vec.leftSemimodule {n})
  module MatR {n} = MkRightSemimodule semiring (Vec.rightSemimodule {n})

open MatL public
open MatR public

