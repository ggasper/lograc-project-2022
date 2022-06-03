{-
  The definition and proof of the lambek lemma.
-}
module Lambek where

open import Level
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor.Algebra
open import Categories.Functor
open import Categories.Morphism.Reasoning
open import Categories.Object.Initial
open import FAlgebraCategory
open import PolynomialFunctor

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} (F : Endofunctor  C) (I : Initial (F-algebra-category F)) where
  open Category C renaming (_≈_ to _≈ᶜ_; id to idᶜ; assoc to assocᶜ; sym-assoc to sym-assocᶜ;
    identityˡ to identityˡᶜ; identityʳ to identityʳᶜ; identity² to identity²ᶜ; equiv to equivᶜ;
    ∘-resp-≈ to ∘-resp-≈ᶜ ; ∘-resp-≈ʳ to ∘-resp-≈ʳᶜ ; _⇒_ to _⇒ᶜ_ ; _∘_ to _∘ᶜ_)
  open import Categories.Morphism C
  open HomReasoning
  open Initial I renaming (⊥ to μF ; ⊥-is-initial to μF-is-initial)
  open Functor F renaming (identity to identity-F)
  open IsInitial μF-is-initial renaming (! to μF→B ; !-unique₂ to μF→B-unique₂)
  open F-Algebra μF

  lambek-lemma : F₀ A ≅ A
  lambek-lemma = record { 
    from = α ; 
    to = i ; 
    iso = record { 
      isoˡ = isoˡ-aux ; 
      isoʳ = isoʳ-aux 
      }
    }

    where
      {-
        The morphism in the F-algebra category between F-algebras
        μF and F ( μF ) where μF is the initial object.
        Exists because μF is the initial object.
      -}
      i-morphism : 
        (F-algebra-category F Category.⇒ μF)
        (record { A = F₀ A ; α = F₁ α })
      i-morphism = μF→B {record 
                        { A = F₀ A ;
                          α = F₁ α}
                        }
      open F-Algebra-Morphism i-morphism renaming (f to i)

      -- The identity morphism from the initial algebra μF to μF
      id-f-morph : F-Algebra-Morphism μF μF
      id-f-morph = Category.id (F-algebra-category F)

      i∘α≈F[α∘i] : i ∘ᶜ α ≈ᶜ F₁ (α ∘ᶜ i)  
      i∘α≈F[α∘i] =
        begin
          i ∘ᶜ α
        ≈⟨ commutes ⟩ -- commutativity of the F-algebra morphism i
          F₁ α ∘ᶜ F₁ i
        ≈⟨ Equiv.sym homomorphism ⟩
          F₁ (α ∘ᶜ i)
        ∎

      -- the F-algebra morphism from the initial algebra μF to μF induced by α ∘ i
      α∘i-morph : F-Algebra-Morphism μF μF
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

      {-
        Shows that α ∘ᶜ i ≈ idᶜ by using the uniqueness of the morphism
        from the initial algebra μF to itself and that α ∘ᶜ i, idᶜ are
        both such morphisms.
      -}
      isoʳ-aux : α ∘ᶜ i ≈ᶜ idᶜ
      isoʳ-aux = μF→B-unique₂ α∘i-morph id-f-morph

      {-
        Proof that i ∘ᶜ αᶜ ≈ idᶜ which follows from α ∘ᶜ i ≈ᶜ idᶜ and
        the fact that F₁ (α ∘ᶜ i) = i ∘ᶜ αᶜ.
      -}
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
