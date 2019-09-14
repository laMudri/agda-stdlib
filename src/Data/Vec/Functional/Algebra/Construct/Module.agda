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

open import Data.Nat using (ℕ)
open import Data.Vec.Functional using (Vector)
import Data.Vec.Functional.Algebra.Construct.LeftModule as MkLeftModule

open CommutativeRing commutativeRing

private
  open module Elem = Module elemModule
  open module Prev = MkLeftModule ring Elem.leftModule

module′ : ∀ {n} → Module commutativeRing c ℓ
module′ {n} = record
  { Carrierᴹ = Vector Carrierᴹ n
  ; isModule = record
    { isLeftModule = LeftModule.isLeftModule Prev.leftModule
    }
  }
