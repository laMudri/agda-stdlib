------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting left semimodules of elements to left semimodules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Vec.Functional.Algebra.Construct.LeftSemimodule
  {c ℓ} (semiring : Semiring c ℓ)
  (elemLeftSemimodule : LeftSemimodule semiring c ℓ)
  where

import Algebra.Structures.Module as MS
open import Algebra.FunctionProperties.Core
import Algebra.FunctionProperties.Module.Left as L

open import Data.Nat using (ℕ)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.CommutativeMonoid as MkCommutativeMonoid
open import Relation.Binary

open Semiring semiring

private
  open module Elem = LeftSemimodule elemLeftSemimodule
  open module Prev = MkCommutativeMonoid +ᴹ-commutativeMonoid

module _ {n : ℕ} where

  open CommutativeMonoid (Prev.commutativeMonoid {n = n})
    using ()
    renaming
      ( _≈_                 to _≈̇_
      ; _∙_                 to _+̇_
      ; ε                   to 0̇
      ; isCommutativeMonoid to +̇-isCommutativeMonoid
      )
  open L _≈_ _≈̇_
  open MS _≈̇_

  private
    _*̇ₗ_ : Opₗ Carrier (Vector Carrierᴹ n)
    _*̇ₗ_ x xs = map (x *ₗ_) xs

    *̇ₗ-cong : Congruent _*̇ₗ_
    *̇ₗ-cong p ps i = *ₗ-cong p (ps i)

    *̇ₗ-assoc : Associative _*_ _*̇ₗ_
    *̇ₗ-assoc x y xs i = *ₗ-assoc x y (xs i)

    *̇ₗ-identityˡ : LeftIdentity 1# _*̇ₗ_
    *̇ₗ-identityˡ xs i = *ₗ-identityˡ (xs i)

    *̇ₗ-zeroˡ : LeftZero 0# 0̇ _*̇ₗ_
    *̇ₗ-zeroˡ xs i = *ₗ-zeroˡ (xs i)

    *̇ₗ-distribʳ : _*̇ₗ_ DistributesOverʳ _+_ ⟶ _+̇_
    *̇ₗ-distribʳ xs x y i = *ₗ-distribʳ (xs i) x y

    *̇ₗ-zeroʳ : RightZero 0̇ _*̇ₗ_
    *̇ₗ-zeroʳ x i = *ₗ-zeroʳ x

    *̇ₗ-distribˡ : _*̇ₗ_ DistributesOverˡ _+̇_
    *̇ₗ-distribˡ x xs ys i = *ₗ-distribˡ x (xs i) (ys i)

  leftSemimodule : LeftSemimodule semiring c ℓ
  leftSemimodule = record
    { isLeftSemimodule = record
      { +ᴹ-isCommutativeMonoid = +̇-isCommutativeMonoid
      ; *ₗ-cong                = *̇ₗ-cong
      ; *ₗ-zeroˡ               = *̇ₗ-zeroˡ
      ; *ₗ-distribʳ            = *̇ₗ-distribʳ
      ; *ₗ-identityˡ           = *̇ₗ-identityˡ
      ; *ₗ-assoc               = *̇ₗ-assoc
      ; *ₗ-zeroʳ               = *̇ₗ-zeroʳ
      ; *ₗ-distribˡ            = *̇ₗ-distribˡ
      }
   }
