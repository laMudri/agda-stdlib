------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting algebraic structures pointwise into structures on vectors.
------------------------------------------------------------------------
module Data.Vec.Functional.Algebra.Pointwise where

open import Level
open import Algebra
open import Algebra.Module
open import Algebra.Module.Properties
import Algebra.FunctionProperties.Module.Left as L
import Algebra.FunctionProperties.Module.Right as R
open import Data.Nat using (ℕ)
open import Data.Vec.Functional

import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwise
import Data.Vec.Functional.Algebra.Pointwise.Core as Pointwise

private
  variable c ℓ m mℓ : Level

------------------------------------------------------------------------
-- Addition of vectors

pointwise-magma : Magma c ℓ → ℕ → Magma c ℓ
pointwise-magma magma n = record
  { Carrier = Vector Carrier n
  ; isMagma = record
    { isEquivalence = Pointwise.isEquivalence isEquivalence
    ; ∙-cong        = Pointwise.cong₂ _≈_ _∙_ ∙-cong
    }
  } where open Magma magma

pointwise-semigroup : Semigroup c ℓ → ℕ → Semigroup c ℓ
pointwise-semigroup semigroup n = record
  { isSemigroup = record
    { isMagma = Magma.isMagma (pointwise-magma magma n)
    ; assoc   = Pointwise.assoc _≈_ _∙_ assoc
    }
  } where open Semigroup semigroup

pointwise-monoid : Monoid c ℓ → ℕ → Monoid c ℓ
pointwise-monoid monoid n = record
  { isMonoid = record
    { isSemigroup = Semigroup.isSemigroup (pointwise-semigroup semigroup n)
    ; identity    = Pointwise.identity _≈_ ε _∙_ identity
    }
  } where open Monoid monoid

pointwise-commutativeMonoid : CommutativeMonoid c ℓ → ℕ → CommutativeMonoid c ℓ
pointwise-commutativeMonoid commutativeMonoid n = record
  { isCommutativeMonoid = record
    { isSemigroup = Semigroup.isSemigroup (pointwise-semigroup semigroup n)
    ; identityˡ   = Pointwise.identityˡ _≈_ ε _∙_ identityˡ
    ; comm        = Pointwise.comm _≈_ _∙_ comm
    }
  } where open CommutativeMonoid commutativeMonoid

pointwise-group : Group c ℓ → ℕ → Group c ℓ
pointwise-group group n = record
  { isGroup = record
    { isMonoid = Monoid.isMonoid (pointwise-monoid monoid n)
    ; inverse  = Pointwise.inverse _≈_ ε _⁻¹ _∙_ inverse
    ; ⁻¹-cong  = Pointwise.cong₁ _≈_ _⁻¹ ⁻¹-cong
    }
  } where open Group group

pointwise-abelianGroup : AbelianGroup c ℓ → ℕ → AbelianGroup c ℓ
pointwise-abelianGroup abelianGroup n = record
  { isAbelianGroup = record
    { isGroup = Group.isGroup (pointwise-group group n)
    ; comm    = Pointwise.comm _≈_ _∙_ comm
    }
  } where open AbelianGroup abelianGroup

------------------------------------------------------------------------
-- Scaling of a vector by a scalar

pointwise-leftSemimodule : (semiring : Semiring c ℓ) →
                           LeftSemimodule semiring m mℓ → ℕ → LeftSemimodule semiring m mℓ
pointwise-leftSemimodule semiring leftSemimodule n = record
  { isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = +̇-isCommutativeMonoid
    ; *ₗ-cong                = *̇ₗ-cong
    ; *ₗ-zeroˡ               = *̇ₗ-zeroˡ
    ; *ₗ-distribʳ            = *̇ₗ-distribʳ
    ; *ₗ-identityˡ           = *̇ₗ-identityˡ
    ; *ₗ-assoc               = *̇ₗ-assoc
    ; *ₗ-zeroʳ               = *̇ₗ-zeroʳ
    ; *ₗ-distribˡ            = *̇ₗ-distribˡ
    }
  }
  where
    open Semiring semiring
    open LeftSemimodule leftSemimodule
    open CommutativeMonoid (pointwise-commutativeMonoid +ᴹ-commutativeMonoid n)
      using ()
      renaming
        ( _≈_                 to _≈̇_
        ; _∙_                 to _+̇_
        ; ε                   to 0̇
        ; isCommutativeMonoid to +̇-isCommutativeMonoid
        )
    open L _≈_ _≈̇_

    _*̇ₗ_ : Opₗ Carrier (Vector Carrierᴹ n)
    _*̇ₗ_ x xs = map (x *ₗ_) xs

    *̇ₗ-cong : Congruent _*̇ₗ_
    *̇ₗ-cong p ps i = *ₗ-cong p (ps i)

    *̇ₗ-assoc : Associative _*_ _*̇ₗ_
    *̇ₗ-assoc x y xs i = *ₗ-assoc x y (xs i)

    *̇ₗ-identityˡ : LeftIdentity 1# _*̇ₗ_
    *̇ₗ-identityˡ xs i = *ₗ-identityˡ (xs i)

    *̇ₗ-zeroˡ : LeftZero 0# 0̇ _*̇ₗ_
    *̇ₗ-zeroˡ xs i = *ₗ-zeroˡ (xs i)

    *̇ₗ-distribʳ : _*̇ₗ_ DistributesOverʳ _+_ ⟶ _+̇_
    *̇ₗ-distribʳ xs x y i = *ₗ-distribʳ (xs i) x y

    *̇ₗ-zeroʳ : RightZero 0̇ _*̇ₗ_
    *̇ₗ-zeroʳ x i = *ₗ-zeroʳ x

    *̇ₗ-distribˡ : _*̇ₗ_ DistributesOverˡ _+̇_
    *̇ₗ-distribˡ x xs ys i = *ₗ-distribˡ x (xs i) (ys i)

pointwise-rightSemimodule : (semiring : Semiring c ℓ) →
                            RightSemimodule semiring m mℓ → ℕ → RightSemimodule semiring m mℓ
pointwise-rightSemimodule semiring rightSemimodule n = record
  { isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = +̇-isCommutativeMonoid
    ; *ᵣ-cong                = *̇ᵣ-cong
    ; *ᵣ-zeroˡ               = *̇ᵣ-zeroˡ
    ; *ᵣ-distribʳ            = *̇ᵣ-distribʳ
    ; *ᵣ-identityʳ           = *̇ᵣ-identityʳ
    ; *ᵣ-assoc               = *̇ᵣ-assoc
    ; *ᵣ-zeroʳ               = *̇ᵣ-zeroʳ
    ; *ᵣ-distribˡ            = *̇ᵣ-distribˡ
    }
  }
  where
    open Semiring semiring
    open RightSemimodule rightSemimodule
    open CommutativeMonoid (pointwise-commutativeMonoid +ᴹ-commutativeMonoid n)
      using ()
      renaming
        ( _≈_                 to _≈̇_
        ; _∙_                 to _+̇_
        ; ε                   to 0̇
        ; isCommutativeMonoid to +̇-isCommutativeMonoid
        )
    open R _≈_ _≈̇_

    _*̇ᵣ_ : Opᵣ Carrier (Vector Carrierᴹ n)
    xs *̇ᵣ x = map (_*ᵣ x) xs

    *̇ᵣ-cong : Congruent _*̇ᵣ_
    *̇ᵣ-cong ps p i = *ᵣ-cong (ps i) p

    *̇ᵣ-assoc : Associative _*_ _*̇ᵣ_
    *̇ᵣ-assoc xs x y i = *ᵣ-assoc (xs i) x y

    *̇ᵣ-identityʳ : RightIdentity 1# _*̇ᵣ_
    *̇ᵣ-identityʳ xs i = *ᵣ-identityʳ (xs i)

    *̇ᵣ-zeroʳ : RightZero 0# 0̇ _*̇ᵣ_
    *̇ᵣ-zeroʳ xs i = *ᵣ-zeroʳ (xs i)

    *̇ᵣ-distribˡ : _*̇ᵣ_ DistributesOverˡ _+_ ⟶ _+̇_
    *̇ᵣ-distribˡ xs x y i = *ᵣ-distribˡ (xs i) x y

    *̇ᵣ-zeroˡ : LeftZero 0̇ _*̇ᵣ_
    *̇ᵣ-zeroˡ x i = *ᵣ-zeroˡ x

    *̇ᵣ-distribʳ : _*̇ᵣ_ DistributesOverʳ _+̇_
    *̇ᵣ-distribʳ x xs ys i = *ᵣ-distribʳ x (xs i) (ys i)

pointwise-semimodule : (commutativeSemiring : CommutativeSemiring c ℓ) →
                       Semimodule commutativeSemiring m mℓ → ℕ → Semimodule commutativeSemiring m mℓ
pointwise-semimodule commutativeSemiring semimodule n = record
  { isSemimodule = record
    { isLeftSemimodule = LeftSemimodule.isLeftSemimodule (pointwise-leftSemimodule semiring leftSemimodule n) }
  }
  where
    open CommutativeSemiring commutativeSemiring
    open Semimodule semimodule

pointwise-leftModule : (ring : Ring c ℓ) →
                       LeftModule ring m mℓ → ℕ → LeftModule ring m mℓ
pointwise-leftModule ring leftModule n = record
  { isLeftModule = record
    { isLeftSemimodule = LeftSemimodule.isLeftSemimodule (pointwise-leftSemimodule semiring leftSemimodule n)
    ; -ᴹ‿cong          = -̇‿cong
    ; -ᴹ‿inverse       = -̇‿inverse
    }
  }
  where
    open Ring ring
    open LeftModule leftModule
    open AbelianGroup (pointwise-abelianGroup +ᴹ-abelianGroup n)
      using ()
      renaming
        ( _⁻¹     to -̇_
        ; ⁻¹-cong to -̇‿cong
        ; inverse to -̇‿inverse
        )

pointwise-rightModule : (ring : Ring c ℓ) →
                       RightModule ring m mℓ → ℕ → RightModule ring m mℓ
pointwise-rightModule ring rightModule n = record
  { isRightModule = record
    { isRightSemimodule = RightSemimodule.isRightSemimodule (pointwise-rightSemimodule semiring rightSemimodule n)
    ; -ᴹ‿cong          = -̇‿cong
    ; -ᴹ‿inverse       = -̇‿inverse
    }
  }
  where
    open Ring ring
    open RightModule rightModule
    open AbelianGroup (pointwise-abelianGroup +ᴹ-abelianGroup n)
      using ()
      renaming
        ( _⁻¹     to -̇_
        ; ⁻¹-cong to -̇‿cong
        ; inverse to -̇‿inverse
        )

pointwise-module : (commutativeRing : CommutativeRing c ℓ) →
                   Module commutativeRing m mℓ → ℕ → Module commutativeRing m mℓ
pointwise-module commutativeRing module′ n = record
  { isModule = record
    { isLeftModule = LeftModule.isLeftModule (pointwise-leftModule ring leftModule n) }
  }
  where
    open CommutativeRing commutativeRing
    open Module module′

semiring⇒pointwise-leftSemimodule : (semiring : Semiring c ℓ) → ℕ → LeftSemimodule semiring c ℓ
semiring⇒pointwise-leftSemimodule semiring n =
  pointwise-leftSemimodule semiring (self-leftSemimodule semiring) n

semiring⇒pointwise-rightSemimodule : (semiring : Semiring c ℓ) → ℕ → RightSemimodule semiring c ℓ
semiring⇒pointwise-rightSemimodule semiring n =
  pointwise-rightSemimodule semiring (self-rightSemimodule semiring) n

commutativeSemiring⇒pointwise-semimodule : (commutativeSemiring : CommutativeSemiring c ℓ) → ℕ →
                                           Semimodule commutativeSemiring c ℓ
commutativeSemiring⇒pointwise-semimodule commutativeSemiring n =
  pointwise-semimodule commutativeSemiring (self-semimodule commutativeSemiring) n

ring⇒pointwise-leftModule : (ring : Ring c ℓ) → ℕ → LeftModule ring c ℓ
ring⇒pointwise-leftModule ring n =
  pointwise-leftModule ring (self-leftModule ring) n

ring⇒pointwise-rightModule : (ring : Ring c ℓ) → ℕ → RightModule ring c ℓ
ring⇒pointwise-rightModule ring n =
  pointwise-rightModule ring (self-rightModule ring) n

commutativeRing⇒pointwise-module : (commutativeRing : CommutativeRing c ℓ) → ℕ →
                                   Module commutativeRing c ℓ
commutativeRing⇒pointwise-module commutativeRing n =
  pointwise-module commutativeRing (self-module commutativeRing) n
