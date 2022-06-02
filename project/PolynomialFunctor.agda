{-
  The definition of polynomial functors on the category Sets
-}
module PolynomialFunctor where

open import Level
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor.Algebra
open import Categories.Functor
open import Categories.Morphism.Reasoning
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax ; _×_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b


module _ {o : Level} {I : Set o} (A : I → Set o) where
  open Category (Sets o)
  polynomial-functor : Endofunctor (Sets o)
  polynomial-functor = record
      { F₀ = λ X → Σ[ i ∈ I ] ((A i) → X) -- functor on objects
        ; F₁ = F₁-aux -- functor on morphisms
        ; identity = refl -- F id = id
        ; homomorphism = refl -- F (f ∘ g) = Ff ∘ Fg
        ; F-resp-≈ = F-resp-≈-aux -- f ≈ g ⇒ F₁f ≈ F₁g
      }
    where
      F₁-aux : {A = B : Set o} {C : Set o} →
        Sets o [ B , C ] → 
        Sets o [ 
          Σ-syntax I (λ i → A i → B) , 
          Σ-syntax I (λ i → A i → C) 
          ]
      F₁-aux {A = B} f (i , g) = i , (f ∘ g)

      
      F-resp-≈-aux : 
        {A = B : Set o} 
        {C : Set o} 
        {f g : Sets o [ B , C ]} →
        Sets o [ f ≈ g ] → 
        Sets o [ F₁-aux f ≈ F₁-aux g ]
      F-resp-≈-aux {A = B} p {x = i , h} = 
        cong ( i ,_ ) (fun-ext λ x → p)

