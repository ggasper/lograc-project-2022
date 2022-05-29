module NaturalNumbers where

open import Level renaming (suc to sucₗ ; zero to zeroₗ)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor.Algebra
open import Categories.Functor
open import Categories.Morphism.Reasoning
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax ; _×_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Categories.Object.Initial
open import FAlgebraCategory
open import PolynomialFunctor
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Nat using (ℕ ; suc ; zero)



private
  variable
    o ℓ e : Level

A : Bool → Set
A false = ⊥
A true = ⊤




P : Endofunctor (Sets 0ℓ)
P = polynomial-functor A

P-category : Category (sucₗ zeroₗ ⊔ zeroₗ) (zeroₗ ⊔ zeroₗ) zeroₗ
P-category = F-algebra-category P

Nat-algebra : Category.Obj P-category
Nat-algebra = record { 
    A = ℕ ; 
    α = α-aux }

    where
        α-aux : 
            (Σ Bool (λ i → (x : A i) → ℕ)) 
            → ℕ
        α-aux (false , f) = 0
        α-aux (true , f) = suc ( f tt )


Nat-algebra-initial : Initial P-category
Nat-algebra-initial = record { 
    ⊥ = Nat-algebra ; 
    ⊥-is-initial = record { 
        ! = !-aux  ; 
        !-unique = !-unique-aux
        } }

        where
            f-aux : {B-alg : F-Algebra P} → (Sets 0ℓ Category.⇒ F-Algebra.A Nat-algebra) (F-Algebra.A B-alg)
            f-aux {record { A = B ; α = β }} zero = β (false , (λ ()))
            f-aux {record { A = B ; α = β }} (suc n) =
              β (true , λ _ → f-aux {record { A = B ; α = β }} n)
            

            commutes-aux : {B-alg : F-Algebra P} →
              (Sets 0ℓ Category.≈ (Sets 0ℓ Category.∘ (f-aux {B-alg}))
              (F-Algebra.α Nat-algebra)) ((Sets 0ℓ Category.∘ F-Algebra.α B-alg)
              (Functor.F₁ P (f-aux {B-alg})))
            commutes-aux {B-alg} {false , f} =
              cong (λ x → F-Algebra.α B-alg (false , x)) (fun-ext λ ⊥ → ⊥-elim ⊥)   
            commutes-aux {B-alg} {true , f} = refl


            !-aux : {A = B-alg : F-Algebra P} 
                → (P-category Category.⇒ Nat-algebra) B-alg
            !-aux {B-alg} = record { 
                f = f-aux {B-alg} ; 
                commutes = commutes-aux {B-alg} }
    
            !-unique-aux : {A = B-alg : F-Algebra (polynomial-functor A)}
              (f : F-Algebra-Morphism Nat-algebra B-alg) {x : ℕ} →
              f-aux {B-alg} x ≡ F-Algebra-Morphism.f f x
            !-unique-aux B-alg@{A = record {A = B ; α = β}}
              record { f = f ; commutes = commutes } {zero} =
                begin
                  f-aux {B-alg} zero
                  ≡⟨ refl ⟩
                  f-aux {B-alg} (F-Algebra.α Nat-algebra ( false , λ ()))
                  ≡⟨ cong (λ x → β (false , x)) (fun-ext (λ x → ⊥-elim x)) ⟩
                  (Sets 0ℓ Category.∘ β) (Functor.F₁ P f) (false , (λ ()))
                  ≡⟨ sym (commutes { false , λ () }) ⟩
                  f zero
                ∎
            !-unique-aux {A = B-alg@record { A = B ; α = β }}
              f-morphism@record { f = f ; commutes = commutes } {suc n} =
              begin
                f-aux {B-alg} (suc n)
                ≡⟨ cong (λ x → β ( true , x )) (fun-ext λ x → !-unique-aux f-morphism) ⟩
                β (true , λ _ → f n)
                ≡⟨ sym commutes ⟩
                f (suc n)
              ∎
