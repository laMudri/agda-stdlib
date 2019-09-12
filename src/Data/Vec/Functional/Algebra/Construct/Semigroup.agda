------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semigroups of elements to semigroups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Semigroup {c ℓ} (elemSemigroup : Semigroup c ℓ) where

open import Algebra.Structures
open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Magma as MkMagma

private
  module Elem = Semigroup elemSemigroup

open Elem hiding (isMagma; isSemigroup)
open MkMagma Elem.magma public

module _ {n : ℕ} where

  isSemigroup : IsSemigroup {A = Vector Carrier n} _≈̇_ _∙̇_
  isSemigroup = record
    { isMagma = isMagma
    ; assoc   = Pointwise.assoc _≈_ _∙_ assoc
    }

  semigroup : Semigroup c ℓ
  semigroup  = record
    { Carrier     = Vector Carrier n
    ; isSemigroup = isSemigroup
    }

  scale-assoc : ∀ x y (xs : Vector Carrier n) →
                scale (x ∙ y) xs ≈̇ scale x (scale y xs)
  scale-assoc x y xs i = Elem.assoc x y (xs i)
