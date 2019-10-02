------------------------------------------------------------------------
-- The Agda standard library
--
-- Component functions of permutations found in `Data.Fin.Permutation`
------------------------------------------------------------------------

module Data.Fin.Permutation.Components where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat as ℕ using (zero; suc; _∸_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (P⇒≡true; ¬P⇒≡false)
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties using (Involutive)
open ≡-Reasoning

--------------------------------------------------------------------------------
--  Functions
--------------------------------------------------------------------------------

-- 'tranpose i j' swaps the places of 'i' and 'j'.

transpose : ∀ {n} → Fin n → Fin n → Fin n → Fin n
transpose i j k = if proj₁ (k ≟ i)
  then j
  else if proj₁ (k ≟ j)
    then i
    else k

-- reverse i = n ∸ 1 ∸ i

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (ℕₚ.n∸m≤n (toℕ i) (suc n))

--------------------------------------------------------------------------------
--  Properties
--------------------------------------------------------------------------------

transpose-inverse : ∀ {n} (i j : Fin n) {k} →
                    transpose i j (transpose j i k) ≡ k
transpose-inverse i j {k} with k ≟ j
... | yes p rewrite P⇒≡true (i ≟ i) refl = sym p
... | false , _ with k ≟ i
transpose-inverse i j {k} | false , _ | yes q with j ≟ i
... | yes r = trans r (sym q)
... | false , _ rewrite P⇒≡true (j ≟ j) refl = sym q
transpose-inverse i j {k} | no ¬p | no ¬q
  rewrite ¬P⇒≡false (k ≟ j) ¬p
        | ¬P⇒≡false (k ≟ i) ¬q = refl

reverse-prop : ∀ {n} → (i : Fin n) → toℕ (reverse i) ≡ n ∸ suc (toℕ i)
reverse-prop {zero} ()
reverse-prop {suc n} i = begin
  toℕ (inject≤ (n ℕ- i) _)  ≡⟨ inject≤-lemma _ _ ⟩
  toℕ (n ℕ- i)              ≡⟨ toℕ‿ℕ- n i ⟩
  n ∸ toℕ i                 ∎

reverse-involutive : ∀ {n} → Involutive _≡_ (reverse {n})
reverse-involutive {zero}  ()
reverse-involutive {suc n} i = toℕ-injective (begin
  toℕ (reverse (reverse i)) ≡⟨ reverse-prop (reverse i) ⟩
  n ∸ (toℕ (reverse i))     ≡⟨ cong (n ∸_) (reverse-prop i) ⟩
  n ∸ (n ∸ (toℕ i))         ≡⟨ ℕₚ.m∸[m∸n]≡n (ℕ.≤-pred (toℕ<n i)) ⟩
  toℕ i                     ∎)

reverse-suc : ∀ {n}{i : Fin n} → toℕ (reverse (suc i)) ≡ toℕ (reverse i)
reverse-suc {n} {i} = begin
  toℕ (reverse (suc i))      ≡⟨ reverse-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ sym (reverse-prop i) ⟩
  toℕ (reverse i)            ∎
