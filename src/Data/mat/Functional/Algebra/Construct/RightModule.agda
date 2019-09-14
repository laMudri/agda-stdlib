------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting right modules of elements to right modules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.RightModule
  {c ℓ} (ring : Ring c ℓ)
  (elemRightModule : RightModule ring c ℓ) where

import Data.Vec.Functional.Algebra.Construct.RightModule as MkRightModule

private
  module Vec = MkRightModule ring elemRightModule
  module Mat {n} = MkRightModule ring (Vec.rightModule {n})

open Mat public

