------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting algebraic structures pointwise into structures on matrices.
------------------------------------------------------------------------
module Data.Mat.Functional.Algebra.Pointwise where

open import Level
open import Algebra
open import Algebra.Module
open import Algebra.Module.Properties
open import Data.Nat using (ℕ)
import Data.Vec.Functional.Algebra.Pointwise as Vec

private
  variable c ℓ m mℓ : Level

pointwise-magma : Magma c ℓ → ℕ → ℕ → Magma c ℓ
pointwise-magma magma m n =
  Vec.pointwise-magma (Vec.pointwise-magma magma m) n

pointwise-semigroup : Semigroup c ℓ → ℕ → ℕ → Semigroup c ℓ
pointwise-semigroup semigroup m n =
  Vec.pointwise-semigroup (Vec.pointwise-semigroup semigroup m) n

pointwise-monoid : Monoid c ℓ → ℕ → ℕ → Monoid c ℓ
pointwise-monoid monoid m n =
  Vec.pointwise-monoid (Vec.pointwise-monoid monoid m) n

pointwise-commutativeMonoid : CommutativeMonoid c ℓ → ℕ → ℕ → CommutativeMonoid c ℓ
pointwise-commutativeMonoid commutativeMonoid m n =
  Vec.pointwise-commutativeMonoid (Vec.pointwise-commutativeMonoid commutativeMonoid m) n

pointwise-group : Group c ℓ → ℕ → ℕ → Group c ℓ
pointwise-group group m n =
  Vec.pointwise-group (Vec.pointwise-group group m) n

pointwise-abelianGroup : AbelianGroup c ℓ → ℕ → ℕ → AbelianGroup c ℓ
pointwise-abelianGroup abelianGroup m n =
  Vec.pointwise-abelianGroup (Vec.pointwise-abelianGroup abelianGroup m) n

pointwise-leftSemimodule : (semiring : Semiring c ℓ) →
                           LeftSemimodule semiring m mℓ → ℕ → ℕ → LeftSemimodule semiring m mℓ
pointwise-leftSemimodule semiring leftSemimodule m n =
  Vec.pointwise-leftSemimodule semiring (Vec.pointwise-leftSemimodule semiring leftSemimodule m) n

pointwise-rightSemimodule : (semiring : Semiring c ℓ) →
                            RightSemimodule semiring m mℓ → ℕ → ℕ → RightSemimodule semiring m mℓ
pointwise-rightSemimodule semiring rightSemimodule m n =
  Vec.pointwise-rightSemimodule semiring (Vec.pointwise-rightSemimodule semiring rightSemimodule m) n

pointwise-semimodule : (commutativeSemiring : CommutativeSemiring c ℓ) →
                       Semimodule commutativeSemiring m mℓ → ℕ → ℕ → Semimodule commutativeSemiring m mℓ
pointwise-semimodule commutativeSemiring semimodule m n =
  Vec.pointwise-semimodule commutativeSemiring (Vec.pointwise-semimodule commutativeSemiring semimodule m) n

pointwise-leftModule : (ring : Ring c ℓ) →
                       LeftModule ring m mℓ → ℕ → ℕ → LeftModule ring m mℓ
pointwise-leftModule ring leftModule m n =
  Vec.pointwise-leftModule ring (Vec.pointwise-leftModule ring leftModule m) n

pointwise-rightModule : (ring : Ring c ℓ) →
                       RightModule ring m mℓ → ℕ → ℕ → RightModule ring m mℓ
pointwise-rightModule ring rightModule m n =
  Vec.pointwise-rightModule ring (Vec.pointwise-rightModule ring rightModule m) n

pointwise-module : (commutativeRing : CommutativeRing c ℓ) →
                   Module commutativeRing m mℓ → ℕ → ℕ → Module commutativeRing m mℓ
pointwise-module commutativeRing module′ m n =
  Vec.pointwise-module commutativeRing (Vec.pointwise-module commutativeRing module′ m) n

semiring⇒pointwise-leftSemimodule : (semiring : Semiring c ℓ) → ℕ → ℕ → LeftSemimodule semiring c ℓ
semiring⇒pointwise-leftSemimodule semiring =
  pointwise-leftSemimodule semiring (self-leftSemimodule semiring)

semiring⇒pointwise-rightSemimodule : (semiring : Semiring c ℓ) → ℕ → ℕ → RightSemimodule semiring c ℓ
semiring⇒pointwise-rightSemimodule semiring =
  pointwise-rightSemimodule semiring (self-rightSemimodule semiring)

commutativeSemiring⇒pointwise-semimodule : (commutativeSemiring : CommutativeSemiring c ℓ) → ℕ → ℕ →
                                           Semimodule commutativeSemiring c ℓ
commutativeSemiring⇒pointwise-semimodule commutativeSemiring =
  pointwise-semimodule commutativeSemiring (self-semimodule commutativeSemiring)

ring⇒pointwise-leftModule : (ring : Ring c ℓ) → ℕ → ℕ → LeftModule ring c ℓ
ring⇒pointwise-leftModule ring =
  pointwise-leftModule ring (self-leftModule ring)

ring⇒pointwise-rightModule : (ring : Ring c ℓ) → ℕ → ℕ → RightModule ring c ℓ
ring⇒pointwise-rightModule ring =
  pointwise-rightModule ring (self-rightModule ring)

commutativeRing⇒pointwise-module : (commutativeRing : CommutativeRing c ℓ) → ℕ → ℕ →
                                   Module commutativeRing c ℓ
commutativeRing⇒pointwise-module commutativeRing =
  pointwise-module commutativeRing (self-module commutativeRing)
