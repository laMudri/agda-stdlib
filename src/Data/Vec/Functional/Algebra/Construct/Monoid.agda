------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting monoids of elements to monoids of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Monoid {c ℓ} (elemMonoid : Monoid c ℓ) where

open import Algebra.Structures
open import Data.Nat using (ℕ)
open import Data.Vec.Functional using (Vector; replicate)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Semigroup as MkSemigroup

private
  open module Elem = Monoid elemMonoid
  open module Prev = MkSemigroup Elem.semigroup

monoid : ∀ {n} → Monoid c ℓ
monoid {n} = record
  { Carrier  = Vector Carrier n
  ; ε        = replicate ε
  ; isMonoid = record
    { isSemigroup = Semigroup.isSemigroup Prev.semigroup
    ; identity    = Pointwise.identity _≈_ ε _∙_ identity
    }
  }
