------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting abelian groups of elements to abelian groups of matrices of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Mat.Functional.Algebra.Construct.AbelianGroup {c ℓ} (elemAbelianGroup : AbelianGroup c ℓ) where

import Data.Vec.Functional.Algebra.Construct.AbelianGroup as MkAbelianGroup

private
  module Vec = MkAbelianGroup elemAbelianGroup
  module Mat {n} = MkAbelianGroup (Vec.abelianGroup {n})

open Mat public

