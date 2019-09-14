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
import Algebra.FunctionProperties.Module.Right as R
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Construct.RightSemimodule as MkRightSemimodule
import Data.Vec.Functional.Algebra.Construct.AbelianGroup as MkAbelianGroup

open Ring ring using (semiring; _≈_)
open RightModule elemRightModule using (rightSemimodule; +ᴹ-abelianGroup)
open MkRightSemimodule semiring rightSemimodule public
open MkAbelianGroup +ᴹ-abelianGroup using () renaming (abelianGroup to +̇-abelianGroup)

module _ {n : ℕ} where

  open R _≈_ (_≈̇_ {n = n})
  open MS (_≈̇_ {n = n})

  open AbelianGroup (+̇-abelianGroup {n = n})
    public
    using ()
    renaming
      ( _⁻¹     to -̇_
      ; ⁻¹-cong to -̇‿cong
      ; inverse to -̇‿inverse
      )

  isRightModule : IsRightModule ring _ _ _ _
  isRightModule = record
    { isRightSemimodule = isRightSemimodule
    ; -ᴹ‿cong          = -̇‿cong
    ; -ᴹ‿inverse       = -̇‿inverse
    }

  rightModule : RightModule ring c ℓ
  rightModule = record { isRightModule = isRightModule }
