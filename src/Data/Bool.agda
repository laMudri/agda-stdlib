------------------------------------------------------------------------
-- The Agda standard library
--
-- Booleans
------------------------------------------------------------------------

module Data.Bool where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

------------------------------------------------------------------------
-- The boolean type and some operations

open import Data.Bool.Base public

------------------------------------------------------------------------
-- Queries

infix 4 _≟_

_≟_ : Decidable {A = Bool} _≡_
true  ≟ true  = yes refl
false ≟ false = yes refl
true  ≟ false = no λ()
false ≟ true  = no λ()

------------------------------------------------------------------------
-- Some properties

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_
