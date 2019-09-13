------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative monoids of elements to commutative monoids of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Mat.Functional.Algebra.Construct.CommutativeMonoid {c ℓ} (elemCommutativeMonoid : CommutativeMonoid c ℓ) where

import Data.Vec.Functional.Algebra.Construct.CommutativeMonoid as MkCommutativeMonoid

private
  module Vec = MkCommutativeMonoid elemCommutativeMonoid
  module Mat {n} = MkCommutativeMonoid (Vec.commutativeMonoid {n})

open Mat public

