------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting monoids of elements to monoids of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Mat.Functional.Algebra.Construct.Monoid {c ℓ} (elemMonoid : Monoid c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Monoid as MkMonoid

private
  module Vec = MkMonoid elemMonoid
  module Mat {n} = MkMonoid (Vec.monoid {n})

open Mat public

