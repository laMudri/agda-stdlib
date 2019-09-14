------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semigroups of elements to semigroups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Semigroup {c ℓ} (elemSemigroup : Semigroup c ℓ) where

open import Algebra.Structures
open import Data.Nat using (ℕ)
open import Data.Vec.Functional using (Vector)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Magma as MkMagma

private
  open module Elem = Semigroup elemSemigroup
  open module Prev = MkMagma Elem.magma

semigroup : ∀ {n} → Semigroup c ℓ
semigroup {n} = record
  { Carrier     = Vector Carrier n
  ; isSemigroup = record
    { isMagma = Magma.isMagma Prev.magma
    ; assoc   = Pointwise.assoc _≈_ _∙_ assoc
    }
  }

