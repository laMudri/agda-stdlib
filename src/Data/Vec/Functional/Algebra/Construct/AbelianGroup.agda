------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting Abelian groups of elements to Abelian groups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.AbelianGroup {c ℓ} (elemAbelianGroup : AbelianGroup c ℓ) where

open import Algebra.Structures
open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Group as MkGroup
import Data.Vec.Functional.Algebra.Construct.CommutativeMonoid as MkCommutativeMonoid

private
  open module Elem = AbelianGroup elemAbelianGroup hiding (isAbelianGroup; isGroup)

open MkGroup Elem.group public
open MkCommutativeMonoid Elem.commutativeMonoid public using (scaleₗ-comm; scaleᵣ-comm)

module _ {n : ℕ} where

  isAbelianGroup : IsAbelianGroup {A = Vector Carrier n} _ _ _ _
  isAbelianGroup = record
    { isGroup = isGroup
    ; comm    = Pointwise.comm _≈_ _∙_ comm
    }

  abelianGroup : AbelianGroup c ℓ
  abelianGroup = record
    { Carrier        = Vector Carrier n
    ; isAbelianGroup = isAbelianGroup
    }
