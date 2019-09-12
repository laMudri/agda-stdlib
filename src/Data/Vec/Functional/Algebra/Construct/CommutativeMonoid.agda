------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative monoids of elements to commutative monoids of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.CommutativeMonoid {c ℓ} (elemCommutativeMonoid : CommutativeMonoid c ℓ) where

open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Semigroup as MkSemigroup

open CommutativeMonoid elemCommutativeMonoid

commutativeMonoid : ∀ {n} → CommutativeMonoid c ℓ
commutativeMonoid {n} = record
  { Carrier  = Vector Carrier n
  ; isCommutativeMonoid = record
    { isSemigroup = Semigroup.isSemigroup (MkSemigroup.semigroup semigroup)
    ; identityˡ   = Pointwise.identityˡ _≈_ ε _∙_ identityˡ
    ; comm        = Pointwise.comm _≈_ _∙_ comm
    }
  }
