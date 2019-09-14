------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting modules of elements to modules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Vec.Functional.Algebra.Construct.Module
  {c ℓ} (commutativeRing : CommutativeRing c ℓ)
  (elemModule : Module commutativeRing c ℓ)
  where

import Algebra.Structures.Module as MS
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.LeftModule as MkLeftModule

open CommutativeRing commutativeRing using (ring; _≈_)
open Module elemModule using (leftModule)
open MkLeftModule ring leftModule using (_≈̇_; isLeftModule)

module _ {n : ℕ} where

  open MS (_≈̇_ {n = n})

  isModule : IsModule commutativeRing _ _ _ _
  isModule = record { isLeftModule = isLeftModule }

  module′ : Module commutativeRing c ℓ
  module′ = record { isModule = isModule }
