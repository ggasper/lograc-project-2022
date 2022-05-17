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

  data Tree : Set o where 
    Node : Σ[ i ∈ I ] (A i → Tree) → Tree 

  polynomial-category : Category (suc o ⊔ o) (o ⊔ o) o
  polynomial-category = F-algebra-category (polynomial-functor A)
  open Category polynomial-category 
  open Category (Sets o) renaming (_⇒_ to _⇒ˢ_ ; Obj to Objˢ)

  polynomial-initial : Initial polynomial-category
  polynomial-initial = record { 
    ⊥ = ⊥-aux ;
    ⊥-is-initial = is-initial-aux
    }

    where
      α-aux : (Functor.F₀ (polynomial-functor A) Tree) 
        ⇒ˢ 
        Tree
      α-aux s = Node s

      ⊥-aux : Obj
      ⊥-aux = record { 
        A = Tree ; 
        α = α-aux 
        }

      f-tree-aux : {B : F-Algebra (polynomial-functor A)} → 
        Tree → 
        F-Algebra.A B
      f-tree-aux {record { A = B ; α = β } } (Node (i , g)) = 
        β (
          i , 
          λ a → f-tree-aux {record { A = B ; α = β }} (g a)
          )


      !-aux : {B : F-Algebra (polynomial-functor A)} → F-Algebra-Morphism ⊥-aux B
      !-aux {B} = record { 
        f = f-tree-aux {B} ; 
        commutes = refl 
        }

      !-unique-aux : {A = B : F-Algebra (polynomial-functor A)}
        → (f : F-Algebra-Morphism ⊥-aux B) 
        → (Sets o [ f-tree-aux {B} ≈ F-Algebra-Morphism.f f ])
      !-unique-aux 
        {A = record { A = B ; α = β }} 
        record { f = f ; commutes = commutes }
        {x = Node (i , g)} = 
          begin
            f-tree-aux {record { A = B ; α = β }} (Node (i , g))
          ≡⟨ refl ⟩
            β (i , (λ a → f-tree-aux (g a)))
          ≡⟨ cong 
              (λ x → β (i , x)) 
              (fun-ext λ y → !-unique-aux (record { f = f ; commutes = commutes })) 
            ⟩
            β (i , (λ a → f (g a)))
          ≡⟨ sym commutes ⟩
            f (Node (i , g))
          ∎

      is-initial-aux : IsInitial polynomial-category ⊥-aux
      is-initial-aux = record {   
        ! = !-aux ; 
        !-unique = !-unique-aux 
        }




 