------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting right modules of elements to right modules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Vec.Functional.Algebra.Construct.RightModule
  {c ℓ} (ring : Ring c ℓ)
  (elemRightModule : RightModule ring c ℓ)
  where

import Algebra.Structures.Module as MS
import Algebra.FunctionProperties.Module.Right as L
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.RightSemimodule as MkRightSemimodule
import Data.Vec.Functional.Algebra.Construct.AbelianGroup as MkAbelianGroup

open Ring ring

private
  open module Elem = RightModule elemRightModule
  open module Prev = MkRightSemimodule semiring Elem.rightSemimodule

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

  rightModule : RightModule ring c ℓ
  rightModule = record
    { isRightModule = record
      { isRightSemimodule = RightSemimodule.isRightSemimodule Prev.rightSemimodule
      ; -ᴹ‿cong          = -̇‿cong
      ; -ᴹ‿inverse       = -̇‿inverse
      }
    }
