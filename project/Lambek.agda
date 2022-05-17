module Lambek where

open import Level
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor.Algebra
open import Categories.Functor
open import Categories.Morphism.Reasoning
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax ; _×_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Categories.Object.Initial
open import FAlgebraCategory
open import PolynomialFunctor

open import Categories.Morphism.Reasoning


private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} (F : Endofunctor  C) (I : Initial (F-algebra-category F)) where
  open Category C renaming (_≈_ to _≈ᶜ_; id to idᶜ; assoc to assocᶜ; sym-assoc to sym-assocᶜ; identityˡ to identityˡᶜ; identityʳ to identityʳᶜ; identity² to identity²ᶜ; equiv to equivᶜ; ∘-resp-≈ to ∘-resp-≈ᶜ ; ∘-resp-≈ʳ to ∘-resp-≈ʳᶜ ; _⇒_ to _⇒ᶜ_ ; _∘_ to _∘ᶜ_)
  open import Categories.Morphism C
  open HomReasoning
  open Initial I
  open Functor F renaming (identity to identity-F)
  open IsInitial ⊥-is-initial renaming (! to ⊥→A ; !-unique₂ to ⊥→A-unique₂)
  open F-Algebra ⊥

  LambekLemma : F₀ A ≅ A
  LambekLemma = record { 
    from = α ; 
    to = i ; 
    iso = record { 
      isoˡ = isoˡ-aux ; 
      isoʳ = isoʳ-aux 
      }
    }

    where

      i-morphism : 
        (F-algebra-category F Category.⇒ ⊥) 
        (record { A = F₀ A ; α = F₁ α })
      i-morphism = ⊥→A {record 
                        { A = F₀ A ;
                          α = F₁ α}
                        }
      open F-Algebra-Morphism i-morphism renaming (f to i)


      id-f-morph : F-Algebra-Morphism ⊥ ⊥
      id-f-morph = record { 
        f = idᶜ ; 
        commutes = 
          begin
            idᶜ ∘ᶜ α 
          ≈⟨ identityˡᶜ ⟩
            α
          ≈⟨ Equiv.sym identityʳᶜ ⟩
            α ∘ᶜ idᶜ 
          ≈⟨ ∘-resp-≈ʳᶜ (Equiv.sym identity-F) ⟩
            α ∘ᶜ F₁ idᶜ
          ∎
        }

      i∘α≈F[α∘i] : i ∘ᶜ α ≈ᶜ F₁ (α ∘ᶜ i)  
      i∘α≈F[α∘i] =
        begin
          i ∘ᶜ α
        ≈⟨ commutes ⟩
          F₁ α ∘ᶜ F₁ i
        ≈⟨ Equiv.sym homomorphism ⟩
          F₁ (α ∘ᶜ i)
        ∎

      α∘i-morph : F-Algebra-Morphism ⊥ ⊥
      α∘i-morph = record { 
        f = α ∘ᶜ i ; 
        commutes = 
        begin
          (α ∘ᶜ i) ∘ᶜ α
        ≈⟨ assocᶜ ⟩
          α ∘ᶜ i ∘ᶜ α
        ≈⟨ ∘-resp-≈ʳᶜ i∘α≈F[α∘i] ⟩
          α ∘ᶜ F₁ (α ∘ᶜ i)
        ∎
        }

      isoʳ-aux : α ∘ᶜ i ≈ᶜ idᶜ
      isoʳ-aux = ⊥→A-unique₂ α∘i-morph id-f-morph

      isoˡ-aux : i ∘ᶜ α ≈ᶜ idᶜ
      isoˡ-aux = 
        begin
          i ∘ᶜ α
        ≈⟨ i∘α≈F[α∘i] ⟩
          F₁ (α ∘ᶜ i)
        ≈⟨ F-resp-≈ isoʳ-aux ⟩
          F₁ idᶜ
        ≈⟨ identity-F ⟩
          idᶜ
        ∎