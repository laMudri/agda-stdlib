------------------------------------------------------------------------
-- The Agda standard library
--
-- Products
------------------------------------------------------------------------

module Data.Product where

open import Function
open import Level
open import Relation.Nullary
open import Agda.Builtin.Equality

open import Data.Product.Core public

∄ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄ P = ¬ ∃ P

∄-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B
