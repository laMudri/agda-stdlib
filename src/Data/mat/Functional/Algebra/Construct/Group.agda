------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting groups of elements to groups of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Mat.Functional.Algebra.Construct.Group {c ℓ} (elemGroup : Group c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Group as MkGroup

private
  module Vec = MkGroup elemGroup
  module Mat {n} = MkGroup (Vec.group {n})

open Mat public

