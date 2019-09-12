------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting Abelian groups of elements to Abelian groups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.AbelianGroup {c ℓ} (elemAbelianGroup : AbelianGroup c ℓ) where

open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Group as MkGroup

open AbelianGroup elemAbelianGroup

abelianGroup : ∀ {n} → AbelianGroup c ℓ
abelianGroup {n} = record
  { Carrier  = Vector Carrier n
  ; isAbelianGroup = record
    { isGroup = Group.isGroup (MkGroup.group group)
    ; comm    = Pointwise.comm _≈_ _∙_ comm
    }
  }
