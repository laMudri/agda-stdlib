------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting rings of elements to left and right modules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Ring {c ℓ} (elemRing : Ring c ℓ) where

open import Algebra.Module
open import Algebra.Module.Properties
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.LeftModule as MkLeftModule
import Data.Vec.Functional.Algebra.Construct.RightModule as MkRightModule

private
  module Left = MkLeftModule elemRing (self-leftModule elemRing)
  module Right = MkRightModule elemRing (self-rightModule elemRing)

module _ {n : ℕ} where

  leftModule : LeftModule elemRing c ℓ
  leftModule = Left.leftModule {n = n}

  rightModule : RightModule elemRing c ℓ
  rightModule = Right.rightModule {n = n}
