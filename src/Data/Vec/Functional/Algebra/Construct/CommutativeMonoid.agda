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
import Data.Vec.Functional.Algebra.Construct.Semigroup as MkSemigroup
import Relation.Binary.Reasoning.Setoid as Reasoning

open CommutativeMonoid elemCommutativeMonoid
private
  open module Dummy {n} = Definitions (Vector Carrier n) Carrier _≈_
open Reasoning setoid

commutativeMonoid : ∀ {n} → CommutativeMonoid c ℓ
commutativeMonoid {n} = record
  { Carrier  = Vector Carrier n
  ; isCommutativeMonoid = record
    { isSemigroup = Semigroup.isSemigroup (MkSemigroup.semigroup semigroup)
    ; identityˡ   = Pointwise.identityˡ _≈_ ε _∙_ identityˡ
    ; comm        = Pointwise.comm _≈_ _∙_ comm
    }
  }

∑-homo-0 : ∀ {n} → Homomorphic₀ {n} (foldr _∙_ ε) (replicate ε) ε
∑-homo-0 {zero} = refl
∑-homo-0 {suc n} = trans (identityˡ _) (∑-homo-0 {n})

∑-homo-+ : ∀ {n} → Homomorphic₂ {n} (foldr _∙_ ε) (zipWith _∙_) _∙_
∑-homo-+ {zero} xs ys = sym (identityˡ ε)
∑-homo-+ {suc n} xs ys = begin
  (head xs ∙ head ys) ∙ foldr _∙_ ε (zipWith _∙_ (tail xs) (tail ys))
    ≈⟨ ∙-cong refl (∑-homo-+ {n} (tail xs) (tail ys)) ⟩
  (head xs ∙ head ys) ∙ (foldr _∙_ ε (tail xs) ∙ foldr _∙_ ε (tail ys))
    ≈⟨ rearr _ _ _ _ ⟩
  (head xs ∙ foldr _∙_ ε (tail xs)) ∙ (head ys ∙ foldr _∙_ ε (tail ys))
    ∎
  where
  rearr : ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ y) ∙ (x ∙ z)
  rearr w x y z = begin
    (w ∙ x) ∙ (y ∙ z)  ≈⟨ assoc _ _ _ ⟩
    w ∙ (x ∙ (y ∙ z))  ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    w ∙ ((x ∙ y) ∙ z)  ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
    w ∙ ((y ∙ x) ∙ z)  ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
    w ∙ (y ∙ (x ∙ z))  ≈⟨ sym (assoc _ _ _) ⟩
    (w ∙ y) ∙ (x ∙ z)  ∎
