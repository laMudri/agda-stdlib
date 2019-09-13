------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting rings of elements to left and right modules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Ring {c ℓ} (elemRing : Ring c ℓ) where

open import Algebra.Module
import Algebra.Structures.Module as ModuleS
import Algebra.FunctionProperties as FP
import Algebra.FunctionProperties.Module.Left as LModProp
import Algebra.FunctionProperties.Module.Right as RModProp
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.AbelianGroup as MkAbelianGroup
import Data.Vec.Functional.Algebra.Construct.Semiring as MkSemiring

private
  open module Elem = Ring elemRing

open MkAbelianGroup Elem.+-abelianGroup public
  using ()
  renaming
    ( _⁻̇¹            to -̇_
    ; ⁻̇¹-cong        to -̇‿cong
    ; isGroup        to +̇-isGroup
    ; isAbelianGroup to +̇-isAbelianGroup
    ; group          to +̇-group
    ; abelianGroup   to +̇-abelianGroup
    )
open MkSemiring Elem.semiring public

module _ {n : ℕ} where

  open FP (_≈̇_ {n = n})
  open ModuleS (_≈̇_ {n = n})

  -̇‿inverse : Inverse 0̇ -̇_ _+̇_
  -̇‿inverse = (λ xs i → -‿inverseˡ (xs i))
            , (λ xs i → -‿inverseʳ (xs i))

  isLeftModule : IsLeftModule elemRing _+̇_ scaleₗ 0̇ -̇_
  isLeftModule = record
    { isLeftSemimodule = isLeftSemimodule
    ; -ᴹ‿cong          = -̇‿cong
    ; -ᴹ‿inverse       = -̇‿inverse
    }

  isRightModule : IsRightModule elemRing _+̇_ scaleᵣ 0̇ -̇_
  isRightModule = record
    { isRightSemimodule = isRightSemimodule
    ; -ᴹ‿cong           = -̇‿cong
    ; -ᴹ‿inverse        = -̇‿inverse
    }
