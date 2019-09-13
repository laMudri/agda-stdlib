------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined via index notation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Mat.Functional where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Functional as V using (Vector)
open import Function
open import Level using (Level)

infixl 4 _⊛_

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

Matrix : Set a → (m n : ℕ) → Set a
Matrix A m n = Vector (Vector A n) m

map : (A → B) → ∀ {n} → (Vector A n → Vector B n)
map f M = f ∘ M

rearrange : ∀ {m m′ n n′} → (Fin m′ → Fin m) → (Fin n′ → Fin n) →
            (Matrix A m n → Matrix A m′ n′)
rearrange r s M i j = M (r i) (s j)

row : ∀ {n} → Vector A n → Matrix A 1 n
row xs _ j = xs j

col : ∀ {m} → Vector A m → Matrix A m 1
col xs i _ = xs i

replicate : ∀ {m n} → A → Matrix A m n
replicate x i j = x

_⊛_ : ∀ {m n} → Matrix (A → B) m n → Matrix A m n → Matrix B m n
_⊛_ F M i j = (F i j) (M i j)

zipWith : (A → B → C) → ∀ {m n} → Matrix A m n → Matrix B m n → Matrix C m n
zipWith f M N = replicate f ⊛ M ⊛ N

zip : ∀ {m n} → Matrix A m n → Matrix B m n → Matrix (A × B) m n
zip = zipWith _,_
