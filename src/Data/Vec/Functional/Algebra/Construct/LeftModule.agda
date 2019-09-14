------------------------------------------------------------------------
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

open Ring ring using (semiring; _≈_)
open LeftModule elemLeftModule using (leftSemimodule; +ᴹ-abelianGroup)
open MkLeftSemimodule semiring leftSemimodule public
open MkAbelianGroup +ᴹ-abelianGroup using () renaming (abelianGroup to +̇-abelianGroup)

module _ {n : ℕ} where

  open L _≈_ (_≈̇_ {n = n})
  open MS (_≈̇_ {n = n})

  open AbelianGroup (+̇-abelianGroup {n = n})
    public
    using ()
    renaming
      ( _⁻¹     to -̇_
      ; ⁻¹-cong to -̇‿cong
      ; inverse to -̇‿inverse
      )

  isLeftModule : IsLeftModule ring _ _ _ _
  isLeftModule = record
    { isLeftSemimodule = isLeftSemimodule
    ; -ᴹ‿cong          = -̇‿cong
    ; -ᴹ‿inverse       = -̇‿inverse
    }

  leftModule : LeftModule ring c ℓ
  leftModule = record { isLeftModule = isLeftModule }
