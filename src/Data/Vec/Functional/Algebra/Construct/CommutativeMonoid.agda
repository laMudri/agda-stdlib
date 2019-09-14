------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative monoids of elements to commutative monoids of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.CommutativeMonoid {c ℓ} (elemCommutativeMonoid : CommutativeMonoid c ℓ) where

open import Algebra.Morphism
open import Algebra.Structures
open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Monoid as MkMonoid
import Relation.Binary.Reasoning.Setoid as Reasoning

private
  open module Elem = CommutativeMonoid elemCommutativeMonoid hiding (isCommutativeMonoid; isSemigroup)
  open module Dummy {n} = Definitions (Vector Carrier n) Carrier _≈_

open MkMonoid Elem.monoid public
open Reasoning setoid

module _ {n : ℕ} where

  isCommutativeMonoid : IsCommutativeMonoid {A = Vector Carrier n} _ _ _
  isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; identityˡ   = Pointwise.identityˡ _≈_ ε _∙_ identityˡ
    ; comm        = Pointwise.comm _≈_ _∙_ comm
    }

  commutativeMonoid : CommutativeMonoid c ℓ
  commutativeMonoid = record
    { Carrier  = Vector Carrier n
    ; isCommutativeMonoid = isCommutativeMonoid
    }

{-
  scaleₗ-comm : L.Commutative scaleₗ
  scaleₗ-comm x y xs i = begin
    scaleₗ x (scaleₗ y xs) i ≡⟨⟩
    x ∙ (y ∙ xs i)         ≈⟨ sym (assoc _ _ _) ⟩
    (x ∙ y) ∙ xs i         ≈⟨ ∙-cong (comm _ _) refl ⟩
    (y ∙ x) ∙ xs i         ≈⟨ assoc _ _ _ ⟩
    y ∙ (x ∙ xs i)         ≡⟨⟩
    scaleₗ y (scaleₗ x xs) i ∎

  scaleᵣ-comm : R.Commutative scaleᵣ
  scaleᵣ-comm xs x y i = begin
    scaleᵣ (scaleᵣ xs x) y i ≡⟨⟩
    (xs i ∙ x) ∙ y          ≈⟨ assoc _ _ _ ⟩
    xs i ∙ (x ∙ y)          ≈⟨ ∙-cong refl (comm _ _) ⟩
    xs i ∙ (y ∙ x)          ≈⟨ sym (assoc _ _ _) ⟩
    (xs i ∙ y) ∙ x          ≡⟨⟩
    scaleᵣ (scaleᵣ xs y) x i ∎

  scaleₗ≡scaleᵣ : (x : Carrier) (xs : Vector Carrier n) →
                  scaleₗ x xs ≈̇ scaleᵣ xs x
  scaleₗ≡scaleᵣ x xs i = comm x (xs i)
-}

∑ = foldr _∙_ ε

∑-homo-0 : ∀ {n} → Homomorphic₀ {n} ∑ (replicate ε) ε
∑-homo-0 {zero} = refl
∑-homo-0 {suc n} = trans (identityˡ _) (∑-homo-0 {n})

∑-homo-+ : ∀ {n} → Homomorphic₂ {n} ∑ (zipWith _∙_) _∙_
∑-homo-+ {zero} xs ys = sym (identityˡ ε)
∑-homo-+ {suc n} xs ys = begin
  (head xs ∙ head ys) ∙ ∑ (zipWith _∙_ (tail xs) (tail ys))
    ≈⟨ ∙-cong refl (∑-homo-+ {n} (tail xs) (tail ys)) ⟩
  (head xs ∙ head ys) ∙ (∑ (tail xs) ∙ ∑ (tail ys))
    ≈⟨ exch _ _ _ _ ⟩
  (head xs ∙ ∑ (tail xs)) ∙ (head ys ∙ ∑ (tail ys))
    ∎
  where
  exch : ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ y) ∙ (x ∙ z)
  exch w x y z = begin
    (w ∙ x) ∙ (y ∙ z)  ≈⟨ assoc _ _ _ ⟩
    w ∙ (x ∙ (y ∙ z))  ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    w ∙ ((x ∙ y) ∙ z)  ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
    w ∙ ((y ∙ x) ∙ z)  ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
    w ∙ (y ∙ (x ∙ z))  ≈⟨ sym (assoc _ _ _) ⟩
    (w ∙ y) ∙ (x ∙ z)  ∎
