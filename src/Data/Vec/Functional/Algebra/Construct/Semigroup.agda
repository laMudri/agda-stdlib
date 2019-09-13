------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semigroups of elements to semigroups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Semigroup {c ℓ} (elemSemigroup : Semigroup c ℓ) where

open import Algebra.Structures
import Algebra.FunctionProperties.Module.Left as LModProp
import Algebra.FunctionProperties.Module.Right as RModProp
open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Magma as MkMagma

private
  open module Elem = Semigroup elemSemigroup hiding (isMagma; isSemigroup)

open MkMagma Elem.magma public

module _ {n : ℕ} where

  private
    module L = LModProp _≈_ (_≈̇_ {n = n})
    module R = RModProp _≈_ (_≈̇_ {n = n})

  isSemigroup : IsSemigroup {A = Vector Carrier n} _ _
  isSemigroup = record
    { isMagma = isMagma
    ; assoc   = Pointwise.assoc _≈_ _∙_ assoc
    }

  semigroup : Semigroup c ℓ
  semigroup  = record
    { Carrier     = Vector Carrier n
    ; isSemigroup = isSemigroup
    }

  scaleₗ-assoc : L.Associative _∙_ scaleₗ
  scaleₗ-assoc x y xs i = assoc x y (xs i)

  scaleᵣ-assoc : R.Associative _∙_ scaleᵣ
  scaleᵣ-assoc xs x y i = assoc (xs i) x y
