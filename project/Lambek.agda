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
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


private
  variable
    o ℓ e : Level

-- module _ {C : Category o ℓ e} (F : Endofunctor {o = o} {ℓ = ℓ} {e = e} C) (I : Initial (F-algebra-category {C = Category o ℓ e} F)) where
module _ {C : Category o ℓ e} (F : Endofunctor  C) (I : Initial (F-algebra-category F)) where
  open Category C renaming (_≈_ to _≈ᶜ_; id to idc; assoc to assocᶜ; sym-assoc to sym-assocᶜ; identityˡ to identityˡᶜ; identityʳ to identityʳᶜ; identity² to identity²ᶜ; equiv to equivᶜ; ∘-resp-≈ to ∘-resp-≈ᶜ)
  open import Categories.Morphism C
  -- open Initial I


  LambekLemma : Functor.F₀ F ((F-Algebra.A (Initial.⊥ I))) ≅ F-Algebra.A (Initial.⊥ I)
  LambekLemma = record { 
    from = F-Algebra.α (Initial.⊥ I) ; 
    to = {! F-Algebra-Morphism.f (IsInitial.! (Initial.⊥-is-initial I)) !}; 
    iso = {!   !} 
    }

 