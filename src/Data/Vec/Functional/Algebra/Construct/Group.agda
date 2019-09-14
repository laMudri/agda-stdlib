------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting groups of elements to groups of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Group {c ℓ} (elemGroup : Group c ℓ) where

open import Algebra.Structures
open import Data.Nat using (ℕ)
open import Data.Vec.Functional using (Vector)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Monoid as MkMonoid

private
  open module Elem = Group elemGroup
  open module Prev = MkMonoid Elem.monoid

group : ∀ {n} → Group c ℓ
group {n} = record
  { Carrier = Vector Carrier n
  ; isGroup = record
    { isMonoid = Monoid.isMonoid Prev.monoid
    ; inverse  = Pointwise.inverse _≈_ ε _⁻¹ _∙_ inverse
    ; ⁻¹-cong  = Pointwise.cong₁ _≈_ _⁻¹ ⁻¹-cong
    }
  }

