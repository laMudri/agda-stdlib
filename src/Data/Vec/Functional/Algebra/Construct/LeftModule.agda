-------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting left modules of elements to left modules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Vec.Functional.Algebra.Construct.LeftModule
  {c ℓ} (ring : Ring c ℓ)
  (elemLeftModule : LeftModule ring c ℓ)
  where

import Algebra.Structures.Module as MS
import Algebra.FunctionProperties.Module.Left as L
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.LeftSemimodule as MkLeftSemimodule
import Data.Vec.Functional.Algebra.Construct.AbelianGroup as MkAbelianGroup

open Ring ring

private
  open module Elem = LeftModule elemLeftModule
  open module Prev = MkLeftSemimodule semiring Elem.leftSemimodule

module _ {n : ℕ} where

  open MkAbelianGroup Elem.+ᴹ-abelianGroup
    using ()
    renaming
      ( abelianGroup to +̇-abelianGroup
      )
  open AbelianGroup (+̇-abelianGroup {n = n})
    using ()
    renaming
      ( _⁻¹     to -̇_
      ; ⁻¹-cong to -̇‿cong
      ; inverse to -̇‿inverse
      )

  leftModule : LeftModule ring c ℓ
  leftModule = record
    { isLeftModule = record
      { isLeftSemimodule = LeftSemimodule.isLeftSemimodule Prev.leftSemimodule
      ; -ᴹ‿cong          = -̇‿cong
      ; -ᴹ‿inverse       = -̇‿inverse
      }
    }
