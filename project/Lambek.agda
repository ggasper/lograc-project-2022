module Lambek where

open import Level
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor.Algebra
open import Categories.Functor
open import Categories.Morphism.Reasoning
-- open import Categories.Morphism
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax ; _×_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Categories.Object.Initial
open import AlgebraFunctor
open import PolynomialFunctor

open import Categories.Morphism.Reasoning


private
  variable
    o ℓ e : Level

-- module _ {C : Category o ℓ e} (F : Endofunctor {o = o} {ℓ = ℓ} {e = e} C) (I : Initial (F-algebra-category {C = Category o ℓ e} F)) where
module _ {C : Category o ℓ e} (F : Endofunctor  C) (I : Initial (F-algebra-category F)) where
  open Category C renaming (_≈_ to _≈ᶜ_; id to idc; assoc to assocᶜ; sym-assoc to sym-assocᶜ; identityˡ to identityˡᶜ; identityʳ to identityʳᶜ; identity² to identity²ᶜ; equiv to equivᶜ; ∘-resp-≈ to ∘-resp-≈ᶜ)
  open import Categories.Morphism C
  -- open Initial I
  open HomReasoning

  LambekLemma : Functor.F₀ F ((F-Algebra.A (Initial.⊥ I))) ≅ F-Algebra.A (Initial.⊥ I)
  LambekLemma = record { 
    from = α-map ; 
    to = i-map ; 
    iso = record { 
      isoˡ = {!   !} ; 
      isoʳ = isoʳ-aux 
      }
    }

    where
      α-map : Functor.F₀ F (F-Algebra.A (Initial.⊥ I)) ⇒ F-Algebra.A (Initial.⊥ I)
      α-map = F-Algebra.α (Initial.⊥ I)

      i-morphism : (F-algebra-category F Category.⇒ Initial.⊥ I) 
        (record  { 
        A = Functor.F₀ F (F-Algebra.A (Initial.⊥ I))  ; α = Functor.F₁ F (F-Algebra.α (Initial.⊥ I))  })
      i-morphism = (IsInitial.! 
        (Initial.⊥-is-initial I))
        {record 
          { A = Functor.F₀ F (F-Algebra.A (Initial.⊥ I)) ;
            α = Functor.F₁ F (F-Algebra.α (Initial.⊥ I))}}

      i-map : F-Algebra.A (Initial.⊥ I) ⇒ Functor.F₀ F (F-Algebra.A (Initial.⊥ I)) 
      i-map = F-Algebra-Morphism.f i-morphism



      id-f-morph : F-Algebra-Morphism (Initial.⊥ I) (Initial.⊥ I) 
      id-f-morph = record { 
        f = idc ; 
        commutes = 
          begin
            (idc ∘ F-Algebra.α (Initial.⊥ I)) 
          ≈⟨ identityˡᶜ ⟩
            F-Algebra.α (Initial.⊥ I)
          ≈⟨ Equiv.sym identityʳᶜ ⟩
           (F-Algebra.α (Initial.⊥ I) ∘ idc) 
          ≈⟨ ∘-resp-≈ʳ (Equiv.sym (Functor.identity F))   ⟩
            (F-Algebra.α (Initial.⊥ I) ∘ Functor.F₁ F idc)
          ∎
        }

      α∘i-morph : F-Algebra-Morphism (Initial.⊥ I) (Initial.⊥ I)
      α∘i-morph = record { 
        f = α-map ∘ i-map ; 
        commutes = {! !} 
        }
      
      isoʳ-aux : 
        F-Algebra.α (Initial.⊥ I) 
        ∘ 
        F-Algebra-Morphism.f (IsInitial.! (Initial.⊥-is-initial I)) 
        ≈ᶜ 
        idc
      isoʳ-aux = {!   !}
 