------------------------------------------------------------------------
-- The Agda standard library
--
-- zipWith preserves various algebraic properties, up to Pointwise equality
-- Note that Selective is not preserved.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.Vec.Functional.Algebra.Pointwise.Core
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
  where

open import Algebra.FunctionProperties
open import Data.Fin as F using (Fin)
open import Data.Nat as N using (ℕ)
open import Data.Product as Σ using (_,_; proj₁; proj₂)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise hiding (map)

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

conicalˡ : ∀ 0# _+_ → LeftConical _≈_ 0# _+_ → ∀ {n} →
  LeftConical (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
conicalˡ _ _ con xs ys qs i = con (xs i) (ys i) (qs i)

conicalʳ : ∀ 0# _+_ → RightConical _≈_ 0# _+_ → ∀ {n} →
  RightConical (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
conicalʳ _ _ con xs ys qs i = con (xs i) (ys i) (qs i)

conical : ∀ 0# _+_ → Conical _≈_ 0# _+_ → ∀ {n} →
  Conical (Pointwise _≈_ {n = n}) (replicate 0#) (zipWith _+_)
conical 0# _+_ (conˡ , conʳ) = conicalˡ 0# _+_ conˡ , conicalʳ 0# _+_ conʳ

distribˡ : ∀ _*_ _+_ → _DistributesOverˡ_ _≈_ _*_ _+_ → ∀ {n} →
  _DistributesOverˡ_ (Pointwise _≈_ {n = n}) (zipWith _*_) (zipWith _+_)
distribˡ _ _ d xs ys zs i = d (xs i) (ys i) (zs i)

distribʳ : ∀ _*_ _+_ → _DistributesOverʳ_ _≈_ _*_ _+_ → ∀ {n} →
  _DistributesOverʳ_ (Pointwise _≈_ {n = n}) (zipWith _*_) (zipWith _+_)
distribʳ _ _ d xs ys zs i = d (xs i) (ys i) (zs i)

distrib : ∀ _*_ _+_ → _DistributesOver_ _≈_ _*_ _+_ → ∀ {n} →
  _DistributesOver_ (Pointwise _≈_ {n = n}) (zipWith _*_) (zipWith _+_)
distrib _*_ _+_ (dˡ , dʳ) = distribˡ _*_ _+_ dˡ , distribʳ _*_ _+_ dʳ

idempotent-on : ∀ _∙_ x → _IdempotentOn_ _≈_ _∙_ x → ∀ {n} →
  _IdempotentOn_ (Pointwise _≈_ {n = n}) (zipWith _∙_) (replicate x)
idempotent-on _ _ ide i = ide

idem₂ : ∀ _∙_ → Idempotent _≈_ _∙_ → ∀ {n} →
  Idempotent (Pointwise _≈_ {n = n}) (zipWith _∙_)
idem₂ _∙_ ide xs i = idempotent-on _∙_ (xs i) (ide (xs i)) i

idem₁ : ∀ f → IdempotentFun _≈_ f → ∀ {n} →
  IdempotentFun (Pointwise _≈_ {n = n}) (map f)
idem₁ _ ide xs i = ide (xs i)

absorbs : ∀ _∙_ _∘_ → _Absorbs_ _≈_ _∙_ _∘_ → ∀ {n} →
  _Absorbs_ (Pointwise _≈_ {n = n}) (zipWith _∙_) (zipWith _∘_)
absorbs _ _ abs xs ys i = abs (xs i) (ys i)

absorptive : ∀ _∙_ _∘_ → Absorptive _≈_ _∙_ _∘_ → ∀ {n} →
  Absorptive (Pointwise _≈_ {n = n}) (zipWith _∙_) (zipWith _∘_)
absorptive _∙_ _∘_ (abs , abs′) = absorbs _∙_ _∘_ abs , absorbs _∘_ _∙_ abs′

involutive : ∀ f → Involutive _≈_ f → ∀ {n} →
  Involutive (Pointwise _≈_ {n = n}) (map f)
involutive _ invo xs i = invo (xs i)

cancelˡ : ∀ _+_ → LeftCancellative _≈_ _+_ → ∀ {n} →
  LeftCancellative (Pointwise _≈_ {n = n}) (zipWith _+_)
cancelˡ _ can xs qs i = can (xs i) (qs i)

cancelʳ : ∀ _+_ → RightCancellative _≈_ _+_ → ∀ {n} →
  RightCancellative (Pointwise _≈_ {n = n}) (zipWith _+_)
cancelʳ _ can ys zs qs i = can (ys i) (zs i) (qs i)

cancel : ∀ _+_ → Cancellative _≈_ _+_ → ∀ {n} →
  Cancellative (Pointwise _≈_ {n = n}) (zipWith _+_)
cancel _+_ (canˡ , canʳ) = cancelˡ _+_ canˡ , cancelʳ _+_ canʳ

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
