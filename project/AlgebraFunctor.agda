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
  open Category C renaming (_≈_ to _≈ᶜ_; id to idc; assoc to assocᶜ; sym-assoc to sym-assocᶜ; identityˡ to identityˡᶜ; identityʳ to identityʳᶜ; identity² to identity²ᶜ; equiv to equivᶜ; ∘-resp-≈ to ∘-resp-≈ᶜ)
  open HomReasoning
  open IntroElim C renaming (introʳ to intro-hom)
  F-algebra-category : Category (o ⊔ ℓ) (ℓ ⊔ e) e
  F-algebra-category = record
          { Obj = F-Algebra {o} {ℓ} {e} F
          ; _⇒_ = F-Algebra-Morphism {o} {ℓ} {e} {C} {F}
          ; _≈_ = λ f g → 
            C [ 
              F-Algebra-Morphism.f f 
                ≈ 
              F-Algebra-Morphism.f g 
              ] 
          ; id = id-aux 
          ; _∘_ = composition-aux
          ; assoc = assocᶜ
          ; sym-assoc = sym-assocᶜ
          ; identityˡ = identityˡᶜ
          ; identityʳ = identityʳᶜ
          ; identity² = identity²ᶜ
          ; equiv = λ {A} {B} → 
              record { 
                refl = λ {f} → Equiv.refl ; 
                sym = λ f → Equiv.sym f ; 
                trans = λ f g → Equiv.trans f g 
              }
          ; ∘-resp-≈ = ∘-resp-≈ᶜ
          }
      where

      id-aux : {A : F-Algebra F} → F-Algebra-Morphism A A
      id-aux {A} = 
        record { 
          f = 
            idc ; 
          commutes = 
            begin 
              (idc ∘ F-Algebra.α A) 
            ≈⟨ identityˡᶜ ⟩
              F-Algebra.α A
            ≈⟨ intro-hom (Functor.identity F) ⟩
              (F-Algebra.α A ∘ Functor.F₁ F idc)
            ∎
        }

      composition-aux : {A B D : F-Algebra F} → 
        F-Algebra-Morphism B D → 
        F-Algebra-Morphism A B → 
        F-Algebra-Morphism A D 
      composition-aux {A} {B} {D} f g = 
        record { 
          f = 
            F-Algebra-Morphism.f f ∘ F-Algebra-Morphism.f g ; 
          commutes = 
            begin
              ((F-Algebra-Morphism.f f ∘ F-Algebra-Morphism.f g) ∘ F-Algebra.α A)
            ≈⟨ glue C (F-Algebra-Morphism.commutes f)        (F-Algebra-Morphism.commutes g) ⟩
              (F-Algebra.α D ∘ Functor.F₁ F (F-Algebra-Morphism.f f) ∘ Functor.F₁ F (F-Algebra-Morphism.f g))
            ≈⟨ sym-assocᶜ ⟩
              (((F-Algebra.α D ∘ Functor.F₁ F (F-Algebra-Morphism.f f)) ∘ Functor.F₁ F (F-Algebra-Morphism.f g)))
            ≈⟨ pullʳ C (Equiv.sym (Functor.homomorphism F)) ⟩
              (F-Algebra.α D ∘ Functor.F₁ F (F-Algebra-Morphism.f f ∘ F-Algebra-Morphism.f g))
            ∎ 
          }