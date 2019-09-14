------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting rings of elements to left and right modules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.Ring {c ℓ} (ring : Ring c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Ring as MkRing
import Data.Vec.Functional.Algebra.Construct.LeftModule as MkLeftModule
import Data.Vec.Functional.Algebra.Construct.RightModule as MkRightModule

private
  module Vec = MkRing ring
  module MatL {n} = MkLeftModule ring (Vec.leftModule {n})
  module MatR {n} = MkRightModule ring (Vec.rightModule {n})

open MatL public
open MatR public

