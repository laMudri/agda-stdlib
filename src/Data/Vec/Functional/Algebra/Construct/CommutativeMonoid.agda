------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting commutative monoids of elements to commutative monoids of vectors of elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.Vec.Functional.Algebra.Construct.CommutativeMonoid {c ℓ} (elemCommutativeMonoid : CommutativeMonoid c ℓ) where

open import Algebra.Morphism
open import Data.Nat
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Algebra.Construct.Pointwise as Pointwise
import Data.Vec.Functional.Algebra.Construct.Monoid as MkMonoid
import Relation.Binary.Reasoning.Setoid as Reasoning

private
  open module Elem = CommutativeMonoid elemCommutativeMonoid hiding (isMonoid; isSemigroup)
  open module Dummy {n} = Definitions (Vector Carrier n) Carrier _≈_

open MkMonoid Elem.monoid public
open Reasoning setoid

module _ {n : ℕ} where

  commutativeMonoid : CommutativeMonoid c ℓ
  commutativeMonoid = record
    { Carrier  = Vector Carrier n
    ; isCommutativeMonoid = record
      { isSemigroup = isSemigroup
      ; identityˡ   = Pointwise.identityˡ _≈_ ε _∙_ identityˡ
      ; comm        = Pointwise.comm _≈_ _∙_ comm
      }
    }

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
    ≈⟨ exchange _ _ _ _ ⟩
  (head xs ∙ ∑ (tail xs)) ∙ (head ys ∙ ∑ (tail ys))
    ∎
  where
  exchange : ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ y) ∙ (x ∙ z)
  exchange w x y z = begin
    (w ∙ x) ∙ (y ∙ z)  ≈⟨ assoc _ _ _ ⟩
    w ∙ (x ∙ (y ∙ z))  ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    w ∙ ((x ∙ y) ∙ z)  ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
    w ∙ ((y ∙ x) ∙ z)  ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
    w ∙ (y ∙ (x ∙ z))  ≈⟨ sym (assoc _ _ _) ⟩
    (w ∙ y) ∙ (x ∙ z)  ∎
