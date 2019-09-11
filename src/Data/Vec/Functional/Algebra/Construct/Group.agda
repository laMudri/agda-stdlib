------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting groups of elements to groups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Group {c ℓ} (elemGroup : Group c ℓ) where

open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Monoid as MkMonoid

open Group elemGroup

group : ∀ {n} → Group c ℓ
group {n} = record
  { Carrier = Vector Carrier n
  ; isGroup = record
    { isMonoid = Monoid.isMonoid (MkMonoid.monoid monoid)
    ; inverse  = Pointwise.inverse _≈_ ε _⁻¹ _∙_ inverse
    ; ⁻¹-cong  = Pointwise.cong₁ _≈_ _⁻¹ ⁻¹-cong
    }
  }
