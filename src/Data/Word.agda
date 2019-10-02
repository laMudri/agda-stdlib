------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words
------------------------------------------------------------------------

module Data.Word where

open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base renaming (_≟_ to _≟ℕ_)
open import Data.Product using (proj₁)
import Agda.Builtin.Word as Builtin
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.TrustMe

open Builtin using (Word64) public
open Builtin

toℕ : Word64 → ℕ
toℕ = primWord64ToNat

fromℕ : ℕ → Word64
fromℕ = primWord64FromNat

_≟_ : (a b : Word64) → Dec (a ≡ b)
a ≟ b = if proj₁ (toℕ a ≟ℕ toℕ b)
  then yes trustMe
  else no whatever
  where postulate whatever : _
