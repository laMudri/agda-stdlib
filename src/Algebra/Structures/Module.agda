------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures defined over some other structure
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Structures.Module
  {m ℓm} {M : Set m} (_≈ᴹ_ : Rel M ℓm)
  where

open import Algebra
open import Algebra.FunctionProperties.Core
open import Algebra.FunctionProperties.Module.Core
import Algebra.FunctionProperties as FP
import Algebra.FunctionProperties.Consequences as Consequences
import Algebra.FunctionProperties.Module.Left as L
import Algebra.FunctionProperties.Module.Right as R
open import Algebra.Structures
open import Data.Product using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

module _ {r ℓr} (semiring : Semiring r ℓr) where
  open Semiring semiring renaming (Carrier to R)

  record IsLeft_─Semimodule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M)
                           : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open L _≈_ _≈ᴹ_
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid _≈ᴹ_ +ᴹ 0ᴹ
      *ₗ-cong : Congruent *ₗ
      *ₗ-zeroˡ : LeftZero 0# 0ᴹ *ₗ
      *ₗ-distribʳ : *ₗ DistributesOverʳ _+_ ⟶ +ᴹ
      *ₗ-identity : Identity 1# *ₗ
      *ₗ-assoc : Associative _*_ *ₗ
      *ₗ-zeroʳ : RightZero 0ᴹ *ₗ
      *ₗ-distribˡ : *ₗ DistributesOverˡ +ᴹ

    open IsCommutativeMonoid +ᴹ-isCommutativeMonoid public
      using ()
      renaming ( assoc to +ᴹ-assoc; comm to +ᴹ-comm; identity to +ᴹ-identity
               ; identityʳ to +ᴹ-identityʳ; identityˡ to +ᴹ-identityˡ
               ; isEquivalence to M-isEquivalence; isMagma to +ᴹ-isMagma
               ; isMonoid to +ᴹ-isMonoid
               ; isPartialEquivalence to M-isPartialEquivalence
               ; isSemigroup to +ᴹ-isSemigroup; refl to M-refl
               ; reflexive to M-reflexive; setoid to M-setoid; sym to M-sym
               ; trans to M-trans; ∙-cong to +ᴹ-cong; ∙-congʳ to +ᴹ-congʳ
               ; ∙-congˡ to +ᴹ-congˡ)

  record IsRight_─Semimodule (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M)
                           : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open R _≈_ _≈ᴹ_
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid _≈ᴹ_ +ᴹ 0ᴹ
      *ᵣ-cong : Congruent *ᵣ
      *ᵣ-zeroʳ : RightZero 0# 0ᴹ *ᵣ
      *ᵣ-distribˡ : *ᵣ DistributesOverˡ _+_ ⟶ +ᴹ
      *ᵣ-identity : Identity 1# *ᵣ
      *ᵣ-assoc : Associative _*_ *ᵣ
      *ᵣ-zeroˡ : LeftZero 0ᴹ *ᵣ
      *ᵣ-distribʳ : *ᵣ DistributesOverʳ +ᴹ

    open IsCommutativeMonoid +ᴹ-isCommutativeMonoid public
      using ()
      renaming ( assoc to +ᴹ-assoc; comm to +ᴹ-comm; identity to +ᴹ-identity
               ; identityʳ to +ᴹ-identityʳ; identityˡ to +ᴹ-identityˡ
               ; isEquivalence to M-isEquivalence; isMagma to +ᴹ-isMagma
               ; isMonoid to +ᴹ-isMonoid
               ; isPartialEquivalence to M-isPartialEquivalence
               ; isSemigroup to +ᴹ-isSemigroup; refl to M-refl
               ; reflexive to M-reflexive; setoid to M-setoid; sym to M-sym
               ; trans to M-trans; ∙-cong to +ᴹ-cong; ∙-congʳ to +ᴹ-congʳ
               ; ∙-congˡ to +ᴹ-congˡ)

module _ {r ℓr} (ring : Ring r ℓr) where
  open Ring ring renaming (Carrier to R)

  record IsLeft_─Module (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M) (-ᴹ : Op₁ M)
                        : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open FP _≈ᴹ_
    field
      isLeftSemimodule : IsLeft semiring ─Semimodule +ᴹ *ₗ 0ᴹ
      -ᴹ‿cong : Congruent₁ -ᴹ
      +ᴹ-inverse : Inverse 0ᴹ -ᴹ +ᴹ

    open IsLeft_─Semimodule isLeftSemimodule public

    +ᴹ-isGroup : IsGroup _≈ᴹ_ +ᴹ 0ᴹ -ᴹ
    +ᴹ-isGroup = record
      { isMonoid = +ᴹ-isMonoid
      ; inverse = +ᴹ-inverse
      ; ⁻¹-cong = -ᴹ‿cong
      }

    open IsGroup +ᴹ-isGroup public
      using ()
      renaming (inverseˡ to +ᴹ-inverseˡ; inverseʳ to +ᴹ-inverseʳ
               ; uniqueˡ-⁻¹ to uniqueˡ‿-ᴹ ; uniqueʳ-⁻¹ to uniqueʳ‿-ᴹ)