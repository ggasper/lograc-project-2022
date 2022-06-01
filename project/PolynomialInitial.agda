{-
  The construction of the initial object in the F-algebra category
-}
module PolynomialInitial where

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
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


module _ {o : Level} {I : Set o} (A : I → Set o) where
  -- The structure representing trees which have children parametrized by Aᵢ
  data Tree : Set o where 
    Node : Σ[ i ∈ I ] (A i → Tree) → Tree 

  -- The F-algebra category of some polynomial functor
  polynomial-category : Category (suc o ⊔ o) (o ⊔ o) o
  polynomial-category = F-algebra-category (polynomial-functor A)
  
  open Category polynomial-category 
  open Category (Sets o) renaming (_⇒_ to _⇒ˢ_ ; Obj to Objˢ)

  -- The definition of the initial object in a polynomial category
  polynomial-initial : Initial polynomial-category
  polynomial-initial = record { 
    ⊥ = μF-aux ;
    ⊥-is-initial = is-initial-aux
    }

    where
      -- The map Σ Tree^(Aᵢ) → Tree
      α-aux : (Functor.F₀ (polynomial-functor A) Tree) 
        ⇒ˢ 
        Tree
      α-aux s = Node s
      
      -- The initial object for the category of the polynomial functor
      μF-aux : Obj
      μF-aux = record { 
        A = Tree ; 
        α = α-aux 
        }

      -- Inductive definition of the function from Tree to any F-algebra of a polynomial functor.
      f-tree-aux : {B : F-Algebra (polynomial-functor A)} → 
        Tree → 
        F-Algebra.A B
      f-tree-aux {B-alg@record { A = B ; α = β } } (Node (i , g)) = 
        β (
          i , 
          λ a → f-tree-aux {B-alg} (g a)
          )

      -- F-algebra morphism from the initial object to any other object in the F-algebra category of a polynomial functor.
      !-aux : {B : F-Algebra (polynomial-functor A)} → F-Algebra-Morphism μF-aux B
      !-aux {B} = record { 
        f = f-tree-aux {B} ; 
        commutes = refl 
        }

      -- Proof that the morphism from the initial object is unique.
      !-unique-aux : {A = B : F-Algebra (polynomial-functor A)}
        → (f : F-Algebra-Morphism μF-aux B) 
        → (Sets o [ f-tree-aux {B} ≈ F-Algebra-Morphism.f f ])
      !-unique-aux 
        {A = B-alg@record { A = B ; α = β }} 
        f-morphism@record { f = f ; commutes = commutes }
        {x = Node (i , g)} = 
          begin
            f-tree-aux {B-alg} (Node (i , g))
          ≡⟨ refl ⟩
            β (i , (λ a → f-tree-aux (g a)))
          ≡⟨ cong 
              (λ x → β (i , x)) 
              (fun-ext λ y → !-unique-aux f-morphism) 
            ⟩
            β (i , (λ a → f (g a)))
          ≡⟨ sym commutes ⟩ -- use the commutativity of the diagram of the F-morphism of f
            f (Node (i , g))
          ∎

      is-initial-aux : IsInitial polynomial-category μF-aux
      is-initial-aux = record {   
        ! = !-aux ; -- function that gives the morphism from the initial object to any other object
        !-unique = !-unique-aux -- uniqueness of said morphism
        }




 
