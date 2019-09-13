------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting magmas of elements to magmas of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Mat.Functional.Algebra.Construct.Magma {c ℓ} (elemMagma : Magma c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Magma as MkMagma

private
  module Vec = MkMagma elemMagma
  module Mat {n} = MkMagma (Vec.magma {n})

open Mat public

