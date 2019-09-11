------------------------------------------------------------------------
-- The Agda standard library
--
-- zipWith preserves various algebraic properties, up to Pointwise equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open import Algebra.FunctionProperties

module Data.Vec.Functional.Algebra.Construct.Pointwise
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

-- open import Algebra
open import Data.Fin as F using (Fin)
open import Data.Nat as N using (ℕ)
open import Data.Product as Σ using (_,_; proj₁; proj₂)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise hiding (map)
open import Level using (Level)

assoc : ∀ _+_ → Associative _≈_ _+_ → ∀ {n} →
  Associative (Pointwise _≈_ {n = n}) (zipWith _+_)
assoc _ a xs ys zs i = a (xs i) (ys i) (zs i)

comm : ∀ _+_ → Commutative _≈_ _+_ → ∀ {n} →
  Commutative (Pointwise _≈_ {n = n}) (zipWith _+_)
comm _ c xs ys i = c (xs i) (ys i)

identityˡ : ∀ 0# _+_ → LeftIdentity _≈_ 0# _+_ → ∀ {n} →
  LeftIdentity (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
identityˡ _ _ iden xs i = iden (xs i)

identityʳ : ∀ 0# _+_ → RightIdentity _≈_ 0# _+_ → ∀ {n} →
  RightIdentity (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
identityʳ _ _ iden xs i = iden (xs i)

identity : ∀ 0# _+_ → Identity _≈_ 0# _+_ → ∀ {n} →
  Identity (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
identity 0# _+_ (idenˡ , idenʳ) =
  identityˡ 0# _+_ idenˡ , identityʳ 0# _+_ idenʳ

zeroˡ : ∀ 0# _*_ → LeftZero _≈_ 0# _*_ → ∀ {n} →
  LeftZero (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _*_)
zeroˡ _ _ ze xs i = ze (xs i)

zeroʳ : ∀ 0# _*_ → RightZero _≈_ 0# _*_ → ∀ {n} →
  RightZero (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _*_)
zeroʳ _ _ ze xs i = ze (xs i)

zero : ∀ 0# _*_ → Zero _≈_ 0# _*_ → ∀ {n} →
  Zero (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _*_)
zero 0# _*_ (zeˡ , zeʳ) = zeroˡ 0# _*_ zeˡ , zeroʳ 0# _*_ zeʳ

inverseˡ : ∀ 0# -_ _+_ → LeftInverse _≈_ 0# -_ _+_ → ∀ {n} →
  LeftInverse (Pointwise _≈_ {n = n}) (replicate 0#) (map -_) (zipWith _+_)
inverseˡ _ _ _ inv xs i = inv (xs i)

inverseʳ : ∀ 0# -_ _+_ → RightInverse _≈_ 0# -_ _+_ → ∀ {n} →
  RightInverse (Pointwise _≈_ {n = n}) (replicate 0#) (map -_) (zipWith _+_)
inverseʳ _ _ _ inv xs i = inv (xs i)

inverse : ∀ 0# -_ _+_ → Inverse _≈_ 0# -_ _+_ → ∀ {n} →
  Inverse (Pointwise _≈_ {n = n}) (replicate 0#) (map -_) (zipWith _+_)
inverse 0# -_ _+_ (invˡ , invʳ) =
  inverseˡ 0# -_ _+_ invˡ , inverseʳ 0# -_ _+_ invʳ

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

congˡ : ∀ _∙_ → LeftCongruent _≈_ _∙_ → ∀ {n} →
  LeftCongruent (Pointwise _≈_ {n = n}) (zipWith _∙_)
congˡ _ c xs i = c (xs i)

congʳ : ∀ _∙_ → RightCongruent _≈_ _∙_ → ∀ {n} →
  RightCongruent (Pointwise _≈_ {n = n}) (zipWith _∙_)
congʳ _ c xs i = c (xs i)

cong₁ : ∀ f → Congruent₁ _≈_ f → ∀ {n} →
  Congruent₁ (Pointwise _≈_ {n = n}) (map f)
cong₁ _ c xs i = c (xs i)

cong₂ : ∀ _∙_ → Congruent₂ _≈_ _∙_ → ∀ {n} →
  Congruent₂ (Pointwise _≈_ {n = n}) (zipWith _∙_)
cong₂ _ c xs ys i = c (xs i) (ys i)
