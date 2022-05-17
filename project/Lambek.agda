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
      isoˡ = isoˡ-aux ; 
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

      i∘α≈Fα∘i : i-map ∘ α-map ≈ᶜ Functor.F₁ F (α-map ∘ i-map)  
      i∘α≈Fα∘i =
        begin
          i-map ∘ F-Algebra.α (Initial.⊥ I)
        ≈⟨ F-Algebra-Morphism.commutes i-morphism ⟩
          Functor.F₁ F (F-Algebra.α (Initial.⊥ I)) ∘ Functor.F₁ F (F-Algebra-Morphism.f i-morphism)
        ≈⟨ Equiv.sym (Functor.homomorphism F) ⟩
          Functor.F₁ F (α-map ∘ i-map)
        ∎

      α∘i-morph : F-Algebra-Morphism (Initial.⊥ I) (Initial.⊥ I)
      α∘i-morph = record { 
        f = α-map ∘ i-map ; 
        commutes = 
        begin
          (α-map ∘ i-map) ∘ F-Algebra.α (Initial.⊥ I)
        ≈⟨ assocᶜ ⟩
          α-map ∘ i-map ∘ F-Algebra.α (Initial.⊥ I)
        ≈⟨ ∘-resp-≈ʳ (i∘α≈Fα∘i) ⟩
          (F-Algebra.α (Initial.⊥ I) ∘ Functor.F₁ F (α-map ∘ i-map))
        ∎
        }
      

      isoʳ-aux : 
        F-Algebra.α (Initial.⊥ I) 
        ∘ 
        F-Algebra-Morphism.f (IsInitial.! (Initial.⊥-is-initial I)) 
        ≈ᶜ 
        idc
      isoʳ-aux = (IsInitial.!-unique₂ (Initial.⊥-is-initial I)) (α∘i-morph) (id-f-morph)

      isoˡ-aux :
        F-Algebra-Morphism.f (IsInitial.! (Initial.⊥-is-initial I)) 
        ∘ 
        F-Algebra.α (Initial.⊥ I) 
        ≈ᶜ 
        idc
      isoˡ-aux = 
        begin
          (F-Algebra-Morphism.f (IsInitial.! (Initial.⊥-is-initial I)) ∘ F-Algebra.α (Initial.⊥ I))
        ≈⟨ i∘α≈Fα∘i ⟩
          Functor.F₁ F (α-map ∘ i-map)
        ≈⟨ Functor.F-resp-≈ F isoʳ-aux ⟩
          Functor.F₁ F idc
        ≈⟨ Functor.identity F ⟩
          idc
        ∎
 