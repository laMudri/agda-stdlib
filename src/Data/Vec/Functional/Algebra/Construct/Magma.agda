------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting magmas of elements to magmas of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Magma {c ℓ} (elemMagma : Magma c ℓ) where

open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwise
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise

open Magma elemMagma

magma : ∀ {n} → Magma c ℓ
magma {n} = record
  { Carrier = Vector Carrier n
  ; _≈_     = Pointwise _≈_
  ; _∙_     = zipWith _∙_
  ; isMagma = record
    { isEquivalence = Pointwise.isEquivalence isEquivalence
    ; ∙-cong        = Pointwise.cong₂ _≈_ _∙_ ∙-cong
    }
  }
