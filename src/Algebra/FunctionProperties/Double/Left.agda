------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary
open import Data.Sum

-- The properties are parameterised by the following "equality"
-- relations

module Algebra.FunctionProperties.Double.Left
  {a b ℓa ℓb} {A : Set a} {B : Set b} (_≈ᴬ_ : Rel A ℓa) (_≈ᴮ_ : Rel B ℓb)
  where

open import Algebra.FunctionProperties.Core
open import Data.Product

------------------------------------------------------------------------
-- Binary operations

open import Algebra.FunctionProperties.Double.Core public

------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ A → Opₗ A B → Set _
Associative _∙ᴬ_ _∙ᴮ_ = ∀ x y m → ((x ∙ᴬ y) ∙ᴮ m) ≈ᴮ (x ∙ᴮ (y ∙ᴮ m))

_DistributesOverˡ_ : Opₗ A B → Op₂ B → Set _
_*_ DistributesOverˡ _+_ =
  ∀ x y z → (x * (y + z)) ≈ᴮ ((x * y) + (x * z))

_DistributesOverʳ_⟶_ : Opₗ A B → Op₂ A → Op₂ B → Set _
_*_ DistributesOverʳ _+ᴬ_ ⟶ _+ᴮ_ =
  ∀ x y z → ((y +ᴬ z) * x) ≈ᴮ ((y * x) +ᴮ (z * x))

LeftZero : A → B → Opₗ A B → Set _
LeftZero zᴬ zᴮ _∙_ = ∀ x → (zᴬ ∙ x) ≈ᴮ zᴮ

RightZero : B → Opₗ A B → Set _
RightZero z _∙_ = ∀ x → (x ∙ z) ≈ᴮ z
