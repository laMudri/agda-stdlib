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
open import Data.Vec.Functional using (Vector)
import Data.Vec.Functional.Algebra.Construct.LeftSemimodule as MkLeftSemimodule

open CommutativeSemiring commutativeSemiring

private
  open module Elem = Semimodule elemSemimodule
  open module Prev = MkLeftSemimodule semiring leftSemimodule

semimodule : ∀ {n} → Semimodule commutativeSemiring c ℓ
semimodule {n} = record
  { Carrierᴹ     = Vector Carrierᴹ n
  ; isSemimodule = record
    { isLeftSemimodule = LeftSemimodule.isLeftSemimodule Prev.leftSemimodule
    }
  }
