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
open import AlgebraFunctor
open import PolynomialFunctor

module _ {o : Level} {I : Set o} (A : I → Set o) where

    data Tree : Set o where
        Node : ( i : I ) → ( A i → Tree ) → Tree 

    polynomial-initial : Initial (F-algebra-category (polynomial-functor A))
    polynomial-initial = record { 
        ⊥ = ⊥-aux ;
        ⊥-is-initial = is-initial-aux
        }

        where
            α-aux : (Sets o Category.⇒ Functor.F₀ (polynomial-functor A) Tree) Tree
            α-aux (i , f) = Node i f

            ⊥-aux : Category.Obj (F-algebra-category (polynomial-functor A))
            ⊥-aux = record { 
                A = Tree ; 
                α = α-aux 
                }

            f-tree-aux : {B : F-Algebra (polynomial-functor A)} → Tree → F-Algebra.A B
            f-tree-aux {record { A = B ; α = β }} (Node i h) = β {!   !}


            !-aux : {B : F-Algebra (polynomial-functor A)} → F-Algebra-Morphism ⊥-aux B
            !-aux {B} = record { 
                f = f-tree-aux {B} ; 
                commutes = {!   !} 
                }

            is-initial-aux : IsInitial (F-algebra-category (polynomial-functor A)) ⊥-aux
            is-initial-aux = record {   
                ! = !-aux ; 
                !-unique = {!   !} 
                }


    

