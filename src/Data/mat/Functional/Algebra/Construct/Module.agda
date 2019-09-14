------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting  modules of elements to  modules of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Mat.Functional.Algebra.Construct.Module
  {c ℓ} (commutativeRing : CommutativeRing c ℓ)
  (elemModule : Module commutativeRing c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Module as MkModule

private
  module Vec = MkModule commutativeRing elemModule
  module Mat {n} = MkModule commutativeRing (Vec.module′ {n})

open Mat public

