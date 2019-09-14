------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting Abelian groups of elements to Abelian groups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.AbelianGroup {c ℓ} (elemAbelianGroup : AbelianGroup c ℓ) where

open import Algebra.Structures
open import Data.Nat using (ℕ)
open import Data.Vec.Functional using (Vector)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Group as MkGroup

private
  open module Elem = AbelianGroup elemAbelianGroup
  open module Prev = MkGroup Elem.group

open MkGroup Elem.group public

abelianGroup : ∀ {n} → AbelianGroup c ℓ
abelianGroup {n} = record
  { Carrier        = Vector Carrier n
  ; isAbelianGroup = record
    { isGroup = Group.isGroup Prev.group
    ; comm    = Pointwise.comm _≈_ _∙_ comm
    }
  }
