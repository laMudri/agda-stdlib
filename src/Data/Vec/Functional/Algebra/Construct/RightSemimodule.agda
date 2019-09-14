------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting right semimodules of elements to right semimodules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Module

module Data.Vec.Functional.Algebra.Construct.RightSemimodule
  {c ℓ} (semiring : Semiring c ℓ)
  (elemRightSemimodule : RightSemimodule semiring c ℓ)
  where

import Algebra.Structures.Module as MS
open import Algebra.FunctionProperties.Core
import Algebra.FunctionProperties.Module.Right as R
open import Data.Nat using (ℕ)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.CommutativeMonoid as MkCommutativeMonoid
open import Relation.Binary

open Semiring semiring

private
  open module Elem = RightSemimodule elemRightSemimodule
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
  open R _≈_ _≈̇_
  open MS _≈̇_

  private
    _*̇ᵣ_ : R.Opᵣ Carrier (Vector Carrierᴹ n)
    xs *̇ᵣ x = map (_*ᵣ x) xs

    *̇ᵣ-cong : Congruent _*̇ᵣ_
    *̇ᵣ-cong ps p i = *ᵣ-cong (ps i) p

    *̇ᵣ-assoc : Associative _*_ _*̇ᵣ_
    *̇ᵣ-assoc xs x y i = *ᵣ-assoc (xs i) x y

    *̇ᵣ-identityʳ : RightIdentity 1# _*̇ᵣ_
    *̇ᵣ-identityʳ xs i = *ᵣ-identityʳ (xs i)

    *̇ᵣ-zeroʳ : RightZero 0# 0̇ _*̇ᵣ_
    *̇ᵣ-zeroʳ xs i = *ᵣ-zeroʳ (xs i)

    *̇ᵣ-distribˡ : _*̇ᵣ_ DistributesOverˡ _+_ ⟶ _+̇_
    *̇ᵣ-distribˡ xs x y i = *ᵣ-distribˡ (xs i) x y

    *̇ᵣ-zeroˡ : LeftZero 0̇ _*̇ᵣ_
    *̇ᵣ-zeroˡ x i = *ᵣ-zeroˡ x

    *̇ᵣ-distribʳ : _*̇ᵣ_ DistributesOverʳ _+̇_
    *̇ᵣ-distribʳ x xs ys i = *ᵣ-distribʳ x (xs i) (ys i)

  rightSemimodule : RightSemimodule semiring c ℓ
  rightSemimodule = record
    { isRightSemimodule = record
      { +ᴹ-isCommutativeMonoid = +̇-isCommutativeMonoid
      ; *ᵣ-cong                = *̇ᵣ-cong
      ; *ᵣ-zeroˡ               = *̇ᵣ-zeroˡ
      ; *ᵣ-distribʳ            = *̇ᵣ-distribʳ
      ; *ᵣ-identityʳ           = *̇ᵣ-identityʳ
      ; *ᵣ-assoc               = *̇ᵣ-assoc
      ; *ᵣ-zeroʳ               = *̇ᵣ-zeroʳ
      ; *ᵣ-distribˡ            = *̇ᵣ-distribˡ
      }
    }
