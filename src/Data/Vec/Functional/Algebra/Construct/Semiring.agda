------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting semirings of elements to left and right semimodules of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.Semiring {c ℓ} (elemSemiring : Semiring c ℓ) where

open import Algebra.Module
import Algebra.Structures.Module as ModuleS
import Algebra.FunctionProperties.Module.Left as LModProp
import Algebra.FunctionProperties.Module.Right as RModProp
open import Data.Nat using (ℕ)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.CommutativeMonoid as MkCommutativeMonoid
import Data.Vec.Functional.Algebra.Construct.Monoid as MkMonoid

private
  open module Elem = Semiring elemSemiring

open MkCommutativeMonoid +-commutativeMonoid public
  hiding
    ( scaleₗ
    ; scaleₗ-cong
    ; scaleₗ-assoc
    ; scaleₗ-identityˡ
    ; scaleₗ-comm
    ; scaleᵣ
    ; scaleᵣ-cong
    ; scaleᵣ-assoc
    ; scaleᵣ-identityʳ
    ; scaleᵣ-comm
    )
  renaming
    ( _∙̇_                 to _+̇_
    ; ε̇                   to 0̇
    ; isCommutativeMonoid to +̇-isCommutativeMonoid
    ; isMonoid            to +̇-isMonoid
    ; isSemigroup         to +̇-isSemigroup
    ; isMagma             to +̇-isMagma
    ; commutativeMonoid   to +̇-commutativeMonoid
    ; monoid              to +̇-monoid
    ; semigroup           to +̇-semigroup
    ; magma               to +̇-magma
    )
open MkMonoid *-monoid public
  hiding (_≈̇_)
  renaming
    ( _∙̇_         to _*̇_
    ; ε̇           to 1̇
    ; isMonoid    to *̇-isMonoid
    ; isSemigroup to *̇-isSemigroup
    ; isMagma     to *̇-isMagma
    ; monoid      to *̇-monoid
    ; semigroup   to *̇-semigroup
    ; magma       to *̇-magma
    )

module _ {n : ℕ} where

  open ModuleS (_≈̇_ {n = n})

  private
    module L = LModProp _≈_ (_≈̇_ {n = n})
    module R = RModProp _≈_ (_≈̇_ {n = n})

  scaleₗ-zeroˡ : L.LeftZero 0# 0̇ scaleₗ
  scaleₗ-zeroˡ xs i = zeroˡ (xs i)

  scaleₗ-distribʳ : scaleₗ L.DistributesOverʳ _+_ ⟶ _+̇_
  scaleₗ-distribʳ xs x y i = distribʳ (xs i) x y

  scaleₗ-zeroʳ : L.RightZero 0̇ scaleₗ
  scaleₗ-zeroʳ x i = zeroʳ x

  scaleₗ-distribˡ : scaleₗ L.DistributesOverˡ _+̇_
  scaleₗ-distribˡ x xs ys i = distribˡ x (xs i) (ys i)

  isLeftSemimodule : IsLeftSemimodule elemSemiring _+̇_ scaleₗ 0̇
  isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = +̇-isCommutativeMonoid
    ; *ₗ-cong                = scaleₗ-cong
    ; *ₗ-zeroˡ               = scaleₗ-zeroˡ
    ; *ₗ-distribʳ            = scaleₗ-distribʳ
    ; *ₗ-identityˡ           = scaleₗ-identityˡ
    ; *ₗ-assoc               = scaleₗ-assoc
    ; *ₗ-zeroʳ               = scaleₗ-zeroʳ
    ; *ₗ-distribˡ            = scaleₗ-distribˡ
    }

  leftSemimodule : LeftSemimodule elemSemiring c ℓ
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  scaleᵣ-zeroʳ : R.RightZero 0# 0̇ scaleᵣ
  scaleᵣ-zeroʳ xs i = zeroʳ (xs i)

  scaleᵣ-distribˡ : scaleᵣ R.DistributesOverˡ _+_ ⟶ _+̇_
  scaleᵣ-distribˡ xs x y i = distribˡ (xs i) x y

  scaleᵣ-zeroˡ : R.LeftZero 0̇ scaleᵣ
  scaleᵣ-zeroˡ x i = zeroˡ x

  scaleᵣ-distribʳ : scaleᵣ R.DistributesOverʳ _+̇_
  scaleᵣ-distribʳ x xs ys i = distribʳ x (xs i) (ys i)

  isRightSemimodule : IsRightSemimodule elemSemiring _+̇_ scaleᵣ 0̇
  isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = +̇-isCommutativeMonoid
    ; *ᵣ-cong                = scaleᵣ-cong
    ; *ᵣ-zeroʳ               = scaleᵣ-zeroʳ
    ; *ᵣ-distribˡ            = scaleᵣ-distribˡ
    ; *ᵣ-identityʳ           = scaleᵣ-identityʳ
    ; *ᵣ-assoc               = scaleᵣ-assoc
    ; *ᵣ-zeroˡ               = scaleᵣ-zeroˡ
    ; *ᵣ-distribʳ            = scaleᵣ-distribʳ
    }

  rightSemimodule : RightSemimodule elemSemiring c ℓ
  rightSemimodule = record { isRightSemimodule = isRightSemimodule }
