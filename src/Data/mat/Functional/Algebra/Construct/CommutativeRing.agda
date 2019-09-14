------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative rings of elements to semimodules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.CommutativeRing
  {c ℓ} (commutativeRing : CommutativeRing c ℓ)
  where

import Data.Vec.Functional.Algebra.Construct.CommutativeRing as MkCommutativeRing
import Data.Vec.Functional.Algebra.Construct.Module as MkModule

private
  module Vec = MkCommutativeRing commutativeRing
  module Mat {n} = MkModule commutativeRing (Vec.module′ {n})

open Mat public

