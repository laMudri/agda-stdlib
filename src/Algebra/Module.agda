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

record Left_─Semimodule {r ℓr} (semiring : Semiring r ℓr) m ℓm
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
    isLeftSemimodule : IsLeft semiring ─Semimodule _+ᴹ_ _*ₗ_ 0ᴹ

  open IsLeft_─Semimodule isLeftSemimodule public

record Left_─Module {r ℓr} (ring : Ring r ℓr) m ℓm
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
    isLeftModule : IsLeft ring ─Module _+ᴹ_ _*ₗ_ 0ᴹ -ᴹ_

  open IsLeft_─Module isLeftModule public

record Right_─Semimodule {r ℓr} (semiring : Semiring r ℓr) m ℓm
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
    isRightSemimodule : IsRight semiring ─Semimodule _+ᴹ_ _*ᵣ_ 0ᴹ

  open IsRight_─Semimodule isRightSemimodule public

record _─Semimodule {r ℓr} (commutativeSemiring : CommutativeSemiring r ℓr) m ℓm
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
    isLeftSemimodule : IsLeft semiring ─Semimodule _+ᴹ_ _*ₗ_ 0ᴹ

  open IsLeft_─Semimodule isLeftSemimodule public

  private
    module L = LFP _≈_ _≈ᴹ_
    module R = RFP _≈_ _≈ᴹ_

  leftSemimodule : Left semiring ─Semimodule m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  _*ᵣ_ : Opᵣ Carrier Carrierᴹ
  _*ᵣ_ = flip _*ₗ_

  *ₗ-comm : L.Commutative _*ₗ_
  *ₗ-comm x y m =
    M-trans (M-sym (*ₗ-assoc x y m))
            (M-trans (*ₗ-cong (*-comm _ _) M-refl)
                     (*ₗ-assoc y x m))

  rightSemimodule : Right semiring ─Semimodule m ℓm
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
