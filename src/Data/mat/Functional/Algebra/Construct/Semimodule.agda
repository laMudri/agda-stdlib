------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting  semimodules of elements to  semimodules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.Semimodule
  {c ℓ} (commutativeSemiring : CommutativeSemiring c ℓ)
  (elemSemimodule : Semimodule commutativeSemiring c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Semimodule as MkSemimodule

private
  module Vec = MkSemimodule commutativeSemiring elemSemimodule
  module Mat {n} = MkSemimodule commutativeSemiring (Vec.semimodule {n})

open Mat public

