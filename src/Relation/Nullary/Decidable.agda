------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

module Relation.Nullary.Decidable where

open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_; module Π)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Function.Injection using (Injection; module Injection)
open import Level using (Lift)
open import Relation.Binary using (Setoid; module Setoid; Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Get the boolean value out of the decision without
-- forgetting `P`.
-- `⌊_⌋` should be used in conjunction with `toWitness` and
-- similar functions for proof automation, whereas `proj₁`
-- should be used whenever branching via `if_then_else_`.

⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
⌊ true  , _ ⌋ = true
⌊ false , _ ⌋ = false

True : ∀ {p} {P : Set p} → Dec P → Set
True Q = T ⌊ Q ⌋

False : ∀ {p} {P : Set p} → Dec P → Set
False Q = T (not ⌊ Q ⌋)

-- Gives a witness to the "truth".

toWitness : ∀ {p} {P : Set p} {Q : Dec P} → True Q → P
toWitness {Q = true  , true p} _  = p
toWitness {Q = false , _     } ()

-- Establishes a "truth", given a witness.

fromWitness : ∀ {p} {P : Set p} {Q : Dec P} → P → True Q
fromWitness {Q = true  , _       } = const _
fromWitness {Q = false , false ¬p} = ¬p

-- Variants for False.

toWitnessFalse : ∀ {p} {P : Set p} {Q : Dec P} → False Q → ¬ P
toWitnessFalse {Q = true  , _       }  ()
toWitnessFalse {Q = false , false ¬p} _  = ¬p

fromWitnessFalse : ∀ {p} {P : Set p} {Q : Dec P} → ¬ P → False Q
fromWitnessFalse {Q = true  , true p} = flip _$_ p
fromWitnessFalse {Q = false , _     } = const _

map : ∀ {p q} {P : Set p} {Q : Set q} → P ⇔ Q → Dec P → Dec Q
map P⇔Q p? .proj₁ = p? .proj₁
map P⇔Q (yes p) .proj₂ = true (Equivalence.to P⇔Q ⟨$⟩ p)
map P⇔Q (no ¬p) .proj₂ = false (¬p ∘ _⟨$⟩_ (Equivalence.from P⇔Q))

map′ : ∀ {p q} {P : Set p} {Q : Set q} →
       (P → Q) → (Q → P) → Dec P → Dec Q
map′ P→Q Q→P = map (equivalence P→Q Q→P)

module _ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} where

  open Injection
  open Setoid A using () renaming (_≈_ to _≈A_)
  open Setoid B using () renaming (_≈_ to _≈B_)

  -- If there is an injection from one setoid to another, and the
  -- latter's equivalence relation is decidable, then the former's
  -- equivalence relation is also decidable.

  via-injection : Injection A B → Decidable _≈B_ → Decidable _≈A_
  via-injection inj dec x y =
    map′ (Injection.injective inj) (Π.cong (to inj))
         (dec (to inj ⟨$⟩ x) (to inj ⟨$⟩ y))

module _ {p} {P : Set p} where

  -- If a decision procedure returns "yes", then we can extract the
  -- proof using from-yes.

  From-yes : Dec P → Set p
  From-yes (true  , _) = P
  From-yes (false , _) = Lift ⊤

  from-yes : (p : Dec P) → From-yes p
  from-yes (yes     p) = p
  from-yes (false , _) = _

  -- If a decision procedure returns "no", then we can extract the proof
  -- using from-no.

  From-no : Dec P → Set p
  From-no (false , _) = ¬ P
  From-no (true  , _) = Lift ⊤

  from-no : (p : Dec P) → From-no p
  from-no (no    ¬p) = ¬p
  from-no (true , _) = _

  -- If we know whether the thing we're deciding is true, we can say
  -- what the result of the decision will be.

  P⇒≡true : (P? : Dec P) → P → proj₁ P? ≡ true
  P⇒≡true (true , _) _ = refl
  P⇒≡true (no    ¬p) p = ⊥-elim (¬p p)

  ¬P⇒≡false : (P? : Dec P) → ¬ P → proj₁ P? ≡ false
  ¬P⇒≡false (false , _)  _ = refl
  ¬P⇒≡false (yes     p) ¬p = ⊥-elim (¬p p)
