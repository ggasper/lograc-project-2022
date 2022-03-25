module AlgebraFunctor where

open import Level
open import Categories.Category using (Category)
open import Categories.Functor.Algebra
open import Categories.Functor
open import Function renaming (id to idf)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} (F : Endofunctor C) where
  open Category C renaming (_≈_ to _≈ᶜ_; id to idc)
  F-algebra-category : Category {!!} {!!} {!!}
  F-algebra-category = record
                         { Obj = F-Algebra F
                         ; _⇒_ = F-Algebra-Morphism
                         ; _≈_ = λ f g → F-Algebra-Morphism.f f ≈ᶜ F-Algebra-Morphism.f g -- _≈-aux_
                         ; id = id-aux --id-aux
                         ; _∘_ = {!!}
                         ; assoc = {!!}
                         ; sym-assoc = {!!}
                         ; identityˡ = {!!}
                         ; identityʳ = {!!}
                         ; identity² = {!!}
                         ; equiv = {!!}
                         ; ∘-resp-≈ = {!!}
                         }
                     where
                       commutes-aux : {A : F-Algebra F} →  (C Category.∘ idc) (F-Algebra.α A) ≈ᶜ (C Category.∘ F-Algebra.α A) (Functor.F₁ F idc)
                       commutes-aux = {!!}

                       id-aux : {A : F-Algebra F} → F-Algebra-Morphism A A
                       id-aux = record { f = idc ; commutes = commutes-aux }
