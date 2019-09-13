------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting magmas of elements to magmas of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Magma {c ℓ} (elemMagma : Magma c ℓ) where

open import Algebra.Structures
open import Algebra.FunctionProperties.Core
open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwise
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
open import Relation.Binary

private
  open module Elem = Magma elemMagma hiding (isMagma)

module _ {n : ℕ} where

  _≈̇_ : Rel (Vector Carrier n) ℓ
  _≈̇_ = Pointwise _≈_

  _∙̇_ : Op₂ (Vector Carrier n)
  _∙̇_ = zipWith _∙_

  isMagma : IsMagma _≈̇_ _∙̇_
  isMagma = record
    { isEquivalence = Pointwise.isEquivalence isEquivalence
    ; ∙-cong        = Pointwise.cong₂ _≈_ _∙_ ∙-cong
    }

  magma : Magma c ℓ
  magma = record
    { Carrier = Vector Carrier n
    ; _≈_     = _≈̇_
    ; _∙_     = _∙̇_
    ; isMagma = isMagma
    }

  scale : Carrier → Vector Carrier n → Vector Carrier n
  scale x xs = map (x ∙_) xs
