------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting right semimodules of elements to right semimodules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.RightSemimodule
  {c ℓ} (semiring : Semiring c ℓ)
  (elemRightSemimodule : RightSemimodule semiring c ℓ) where

import Data.Vec.Functional.Algebra.Construct.RightSemimodule as MkRightSemimodule

private
  module Vec = MkRightSemimodule semiring elemRightSemimodule
  module Mat {n} = MkRightSemimodule semiring (Vec.rightSemimodule {n})

open Mat public

