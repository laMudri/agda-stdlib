------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module where

open import Algebra
import Algebra.Structures.Module as Str
open import Algebra.FunctionProperties.Core
open import Algebra.FunctionProperties.Module.Core
import Algebra.FunctionProperties.Module.Left as LFP
import Algebra.FunctionProperties.Module.Right as RFP
open import Function
open import Level
open import Relation.Binary

record LeftSemimodule {r ℓr} (semiring : Semiring r ℓr) m ℓm
                      : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Semiring semiring

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isLeftSemimodule : IsLeftSemimodule semiring _+ᴹ_ _*ₗ_ 0ᴹ

  open IsLeftSemimodule isLeftSemimodule public

record LeftModule {r ℓr} (ring : Ring r ℓr) m ℓm
                  : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Ring ring

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isLeftModule : IsLeftModule ring _+ᴹ_ _*ₗ_ 0ᴹ -ᴹ_

  open IsLeftModule isLeftModule public

record RightSemimodule {r ℓr} (semiring : Semiring r ℓr) m ℓm
                       : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Semiring semiring

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᵣ_ : Opᵣ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isRightSemimodule : IsRightSemimodule semiring _+ᴹ_ _*ᵣ_ 0ᴹ

  open IsRightSemimodule isRightSemimodule public

record Semimodule {r ℓr} (commutativeSemiring : CommutativeSemiring r ℓr) m ℓm
                  : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open CommutativeSemiring commutativeSemiring
  infixr 7 _*ₗ_
  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isLeftSemimodule : IsLeftSemimodule semiring _+ᴹ_ _*ₗ_ 0ᴹ

  open IsLeftSemimodule isLeftSemimodule public

  private
    module L = LFP _≈_ _≈ᴹ_
    module R = RFP _≈_ _≈ᴹ_

  leftSemimodule : LeftSemimodule semiring m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  _*ᵣ_ : Opᵣ Carrier Carrierᴹ
  _*ᵣ_ = flip _*ₗ_

  *ₗ-comm : L.Commutative _*ₗ_
  *ₗ-comm x y m =
    M-trans (M-sym (*ₗ-assoc x y m))
            (M-trans (*ₗ-cong (*-comm _ _) M-refl)
                     (*ₗ-assoc y x m))

  *ᵣ-comm : R.Commutative _*ᵣ_
  *ᵣ-comm m x y = *ₗ-comm y x m

  rightSemimodule : RightSemimodule semiring m ℓm
  rightSemimodule = record
    { Carrierᴹ = Carrierᴹ
    ; _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ᵣ_ = _*ᵣ_
    ; 0ᴹ = 0ᴹ
    ; isRightSemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; *ᵣ-cong = flip *ₗ-cong
      ; *ᵣ-zeroʳ = *ₗ-zeroˡ
      ; *ᵣ-distribˡ = λ m x y → *ₗ-distribʳ x y m
      ; *ᵣ-identityʳ = λ m → *ₗ-identityˡ m
      ; *ᵣ-assoc = λ m x y → M-trans (*ₗ-comm y x m) (M-sym (*ₗ-assoc x y m))
      ; *ᵣ-zeroˡ = *ₗ-zeroʳ
      ; *ᵣ-distribʳ = λ m n x → *ₗ-distribˡ x m n
      }
    }

  open RightSemimodule rightSemimodule public
    using ( *ᵣ-cong; *ᵣ-zeroʳ; *ᵣ-distribˡ; *ᵣ-identityʳ; *ᵣ-assoc; *ᵣ-zeroˡ
          ; *ᵣ-distribʳ)
