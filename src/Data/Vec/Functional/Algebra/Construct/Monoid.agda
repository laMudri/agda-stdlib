------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting monoids of elements to monoids of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Monoid {c ℓ} (elemMonoid : Monoid c ℓ) where

open import Algebra.Structures
open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Semigroup as MkSemigroup

private
  open module Elem = Monoid elemMonoid hiding (isSemigroup; isMonoid)

open MkSemigroup Elem.semigroup public

module _ {n : ℕ} where

  ε̇ : Vector Carrier n
  ε̇ = replicate ε

  isMonoid : IsMonoid {A = Vector Carrier n} _ _ _
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity    = Pointwise.identity _≈_ ε _∙_ identity
    }

  monoid : Monoid c ℓ
  monoid = record
    { Carrier  = Vector Carrier n
    ; ε        = ε̇
    ; isMonoid = isMonoid
    }

  scaleₗ-identityˡ : ∀ (xs : Vector Carrier n) →
                     scaleₗ ε xs ≈̇ xs
  scaleₗ-identityˡ xs i = identityˡ (xs i)

  scaleₗ-identityʳ : ∀ (x : Carrier) →
                     scaleₗ x ε̇ ≈̇ replicate x
  scaleₗ-identityʳ x i = identityʳ x
