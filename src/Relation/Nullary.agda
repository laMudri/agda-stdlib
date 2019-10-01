------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Data.Empty hiding (⊥-elim)
open import Data.Empty.Irrelevant
open import Level

-- Negation.

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

-- `Reflects` idiom: the truth value of P is reflected by a
-- boolean value.

data Reflects {p} (P : Set p) : Bool → Set p where
  true  : ( p :   P) → Reflects P true
  false : (¬p : ¬ P) → Reflects P false

-- Decidable relations.
-- This version of `Dec` allows the boolean portion of the
-- value to compute independently from the proof portion.
-- This often allows good computational properties when we
-- only care about the boolean portion.

Dec : ∀ {p} → Set p → Set p
Dec P = Σ Bool (Reflects P)

pattern yes p = true , true p
pattern no ¬p = false , false ¬p

-- Given an irrelevant proof of a decidable type, a proof can
-- be recomputed and subsequently used in relevant contexts.
recompute : ∀ {a} {A : Set a} → Dec A → .A → A
recompute (yes x) _ = x
recompute (no ¬p) x = ⊥-elim (¬p x)

