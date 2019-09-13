------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semigroups of elements to semigroups of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Mat.Functional.Algebra.Construct.Semigroup {c ℓ} (elemSemigroup : Semigroup c ℓ) where

import Data.Vec.Functional.Algebra.Construct.Semigroup as MkSemigroup

private
  module Vec = MkSemigroup elemSemigroup
  module Mat {n} = MkSemigroup (Vec.semigroup {n})

open Mat public

