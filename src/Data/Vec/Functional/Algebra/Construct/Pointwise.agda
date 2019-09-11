------------------------------------------------------------------------
-- The Agda standard library
--
-- zipWith preserves various algebraic properties, up to Pointwise equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open import Algebra.FunctionProperties

module Data.Vec.Functional.Algebra.Construct.Pointwise
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_+_ : Op₂ A) where

-- open import Algebra
open import Data.Fin as F using (Fin)
open import Data.Nat as N using (ℕ)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise hiding (map)
open import Level using (Level)

assoc : ∀ {n} → Associative _≈_ _+_ →
  Associative (Pointwise _≈_ {n = n}) (zipWith _+_)
assoc a xs ys zs i = a (xs i) (ys i) (zs i)

comm : ∀ {n} → Commutative _≈_ _+_ →
  Commutative (Pointwise _≈_ {n = n}) (zipWith _+_)
comm = {!!}

identityˡ : ∀ {n} 0# → LeftIdentity _≈_ 0# _+_ →
  LeftIdentity (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
identityˡ = {!!}

identityʳ : ∀ {n} 0# → RightIdentity _≈_ 0# _+_ →
  RightIdentity (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
identityʳ = {!!}

identity : ∀ {n} 0# → Identity _≈_ 0# _+_ →
  Identity (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
identity = {!!}

zeroˡ : ∀ {n} z → LeftZero _≈_ z _+_ →
  LeftZero (Pointwise _≈_ {n = n}) (replicate z) (zipWith _+_)
zeroˡ = {!!}

zeroʳ : ∀ {n} z → RightZero _≈_ z _+_ →
  RightZero (Pointwise _≈_ {n = n}) (replicate z) (zipWith _+_)
zeroʳ = {!!}

zero : ∀ {n} z → Zero _≈_ z _+_ →
  Zero (Pointwise _≈_ {n = n}) (replicate z) (zipWith _+_)
zero = {!!}

inverseˡ : ∀ {n} 0# -_ → LeftInverse _≈_ 0# -_ _+_ →
  LeftInverse (Pointwise _≈_ {n = n}) (replicate 0#) (map -_) (zipWith _+_)
inverseˡ 0# -_ inv xs i = inv (xs i)

inverseʳ : ∀ {n} 0# -_ → RightInverse _≈_ 0# -_ _+_ →
  RightInverse (Pointwise _≈_ {n = n}) (replicate 0#) (map -_) (zipWith _+_)
inverseʳ 0# -_ inv xs i = inv (xs i)

inverse : ∀ {n} 0# -_ → Inverse _≈_ 0# -_ _+_ →
  Inverse (Pointwise _≈_ {n = n}) (replicate 0#) (map -_) (zipWith _+_)
inverse 0# -_ inv = {!!}

-- LeftConical e _∙_ = ∀ x y → (x ∙ y) ≈ e → x ≈ e
-- RightConical e _∙_ = ∀ x y → (x ∙ y) ≈ e → y ≈ e
-- Conical e ∙ = (LeftConical e ∙) × (RightConical e ∙)
-- _*_ DistributesOverˡ _+_ =
--   ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))
-- _*_ DistributesOverʳ _+_ =
--   ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))
-- * DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)
-- _∙_ IdempotentOn x = (x ∙ x) ≈ x
-- Idempotent ∙ = ∀ x → ∙ IdempotentOn x
-- IdempotentFun f = ∀ x → f (f x) ≈ f x
-- Selective _∙_ = ∀ x y → (x ∙ y) ≈ x ⊎ (x ∙ y) ≈ y
-- _∙_ Absorbs _∘_ = ∀ x y → (x ∙ (x ∘ y)) ≈ x
-- Absorptive ∙ ∘ = (∙ Absorbs ∘) × (∘ Absorbs ∙)
-- Involutive f = ∀ x → f (f x) ≈ x
-- LeftCancellative _•_ = ∀ x {y z} → (x • y) ≈ (x • z) → y ≈ z
-- RightCancellative _•_ = ∀ {x} y z → (y • x) ≈ (z • x) → y ≈ z
-- Cancellative _•_ = (LeftCancellative _•_) × (RightCancellative _•_)
-- Congruent₁ f = f Preserves _≈_ ⟶ _≈_

congˡ : ∀ {n} → LeftCongruent _≈_ _+_ →
  LeftCongruent (Pointwise _≈_ {n = n}) (zipWith _+_)
congˡ = {!!}

congʳ : ∀ {n} → RightCongruent _≈_ _+_ →
  RightCongruent (Pointwise _≈_ {n = n}) (zipWith _+_)
congʳ = {!!}

cong : ∀ {n} → Congruent₂ _≈_ _+_ →
  Congruent₂ (Pointwise _≈_ {n = n}) (zipWith _+_)
cong = {!!}
