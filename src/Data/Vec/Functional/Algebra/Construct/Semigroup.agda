------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semigroups of elements to semigroups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Semigroup {c ℓ} (elemSemigroup : Semigroup c ℓ) where

open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Magma as MkMagma

open Semigroup elemSemigroup

semigroup : ∀ {n} → Semigroup c ℓ
semigroup {n} = record
  { Carrier     = Vector Carrier n
  ; isSemigroup = record
    { isMagma = Magma.isMagma (MkMagma.magma magma)
    ; assoc   = Pointwise.assoc _≈_ _∙_ assoc
    }
  }
