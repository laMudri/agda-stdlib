------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting left modules of elements to left modules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.LeftModule
  {c ℓ} (ring : Ring c ℓ)
  (elemLeftModule : LeftModule ring c ℓ) where

import Data.Vec.Functional.Algebra.Construct.LeftModule as MkLeftModule

private
  module Vec = MkLeftModule ring elemLeftModule
  module Mat {n} = MkLeftModule ring (Vec.leftModule {n})

open Mat public

