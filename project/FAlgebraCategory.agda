{-
  This file defines the F-Algebra categories
-}

module FAlgebraCategory where
open import Level
open import Categories.Category 
open import Categories.Functor.Algebra
open import Categories.Functor
open import Categories.Morphism.Reasoning

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} (F : Endofunctor C) where
  open Category C renaming (_≈_ to _≈ᶜ_; id to idc; assoc to assocᶜ;
    sym-assoc to sym-assocᶜ; identityˡ to identityˡᶜ; identityʳ to identityʳᶜ;
    identity² to identity²ᶜ; equiv to equivᶜ; ∘-resp-≈ to ∘-resp-≈ᶜ)
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
          ; id = id-aux -- id is the F-algebra that for a given object A consists of A and the identity morphism in the underlying category C
          ; _∘_ = composition-aux -- 
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
          f = idc ; -- the identity in the category C
          commutes = -- proof that idc ∘ α = α ∘ F₁ idc
            begin 
              idc ∘ α
            ≈⟨ identityˡᶜ ⟩
              α
            ≈⟨ intro-hom identity ⟩
              α ∘ F₁ idc
            ∎
        }
        where
          open F-Algebra A
          open Functor F

      composition-aux : {A B D : F-Algebra F} → 
        F-Algebra-Morphism B D → 
        F-Algebra-Morphism A B → 
        F-Algebra-Morphism A D 
      composition-aux {A} {B} {D} f-morphism g-morphism = 
        record { 
          f = f ∘ g ; 
          commutes = 
            begin
              (f ∘ g) ∘ α
            ≈⟨ glue C commutes-f commutes-g ⟩
              β ∘ F₁ f ∘ F₁ g
            ≈⟨ sym-assocᶜ ⟩
              (β ∘ F₁ f) ∘ F₁ g
            ≈⟨ pullʳ C (Equiv.sym homomorphism) ⟩
              β ∘ F₁ (f ∘ g)
            ∎ 
          }
          where
            open F-Algebra-Morphism f-morphism renaming (commutes to commutes-f)
            open F-Algebra-Morphism g-morphism renaming (f to g ; commutes to commutes-g) 
            open Functor F
            open F-Algebra A
            open F-Algebra D renaming (α to β)
