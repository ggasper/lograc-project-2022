module AlgebraFunctor where

open import Level
open import Categories.Category 
open import Categories.Functor.Algebra
open import Categories.Functor
open import Categories.Morphism.Reasoning



private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} (F : Endofunctor C) where
  open Category C renaming (_≈_ to _≈ᶜ_; id to idc)
  open HomReasoning
  open IntroElim C renaming (introʳ to intro-hom)
  open Definitions
  F-algebra-category : Category (o ⊔ ℓ) (ℓ ⊔ e) e
  F-algebra-category = record
          { Obj = F-Algebra {o} {ℓ} {e} F
          ; _⇒_ = F-Algebra-Morphism {o} {ℓ} {e} {C} {F}
          ; _≈_ = λ f g → C [ F-Algebra-Morphism.f f ≈ F-Algebra-Morphism.f g ] 
          ; id = id-aux 
          ; _∘_ = λ f g → record { 
            f = F-Algebra-Morphism.f f ∘ F-Algebra-Morphism.f g ; 
            commutes = glue {!  C !} {!   !} {!   !}  }
            -- commutes = glue {!   !} (F-Algebra-Morphism.commutes f) (F-Algebra-Morphism.commutes g) }
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
      commutes-aux {A} = 
        begin 
        (idc ∘ F-Algebra.α A) 
        ≈⟨ identityˡ ⟩
        F-Algebra.α A
        ≈⟨ intro-hom (Functor.identity F) ⟩
        (F-Algebra.α A ∘ Functor.F₁ F idc)
        ∎

      id-aux : {A : F-Algebra F} → F-Algebra-Morphism A A
      id-aux = record { f = idc ; commutes = commutes-aux }
