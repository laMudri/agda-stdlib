------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting monoids of elements to monoids of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Monoid {c ℓ} (elemMonoid : Monoid c ℓ) where

open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Semigroup as MkSemigroup

open Monoid elemMonoid

monoid : ∀ {n} → Monoid c ℓ
monoid {n} = record
  { Carrier  = Vector Carrier n
  ; ε        = replicate ε
  ; isMonoid = record
    { isSemigroup = Semigroup.isSemigroup (MkSemigroup.semigroup semigroup)
    ; identity    = Pointwise.identity _≈_ ε _∙_ identity
    }
  }
