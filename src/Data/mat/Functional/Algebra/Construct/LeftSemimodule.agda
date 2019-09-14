------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting left semimodules of elements to left semimodules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.LeftSemimodule
  {c ℓ} (semiring : Semiring c ℓ)
  (elemLeftSemimodule : LeftSemimodule semiring c ℓ) where

import Data.Vec.Functional.Algebra.Construct.LeftSemimodule as MkLeftSemimodule

private
  module Vec = MkLeftSemimodule semiring elemLeftSemimodule
  module Mat {n} = MkLeftSemimodule semiring (Vec.leftSemimodule {n})

open Mat public

