------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semimodules of elements to semimodules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Vec.Functional.Algebra.Construct.Semimodule
  {c ℓ} (commutativeSemiring : CommutativeSemiring c ℓ)
  (elemSemimodule : Semimodule commutativeSemiring c ℓ)
  where

import Algebra.Structures.Module as MS
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.LeftSemimodule as MkLeftSemimodule

open CommutativeSemiring commutativeSemiring
open Semimodule elemSemimodule hiding (isSemimodule; isLeftSemimodule)
open MkLeftSemimodule semiring leftSemimodule

module _ {n : ℕ} where

  open MS (_≈̇_ {n = n})

  isSemimodule : IsSemimodule commutativeSemiring _ _ _
  isSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  semimodule : Semimodule commutativeSemiring c ℓ
  semimodule = record { isSemimodule = isSemimodule }
