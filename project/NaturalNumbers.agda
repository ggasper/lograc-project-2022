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

{-
  We show an example of the inductive structure for natural numbers
  by defining an initial object in the F-algebra category 
  of a polynomial functor for a polynomial P ( X ) = 1 + X.
-}
A : Bool → Set
A false = ⊥
A true = ⊤

P : Endofunctor (Sets 0ℓ)
P = polynomial-functor A

P-category : Category (sucₗ zeroₗ ⊔ zeroₗ) (zeroₗ ⊔ zeroₗ) zeroₗ
P-category = F-algebra-category P

open Category P-category
open Category (Sets 0ℓ) renaming (_≈_ to _≈ᶜ_; id to idᶜ; assoc to
  assocᶜ; sym-assoc to sym-assocᶜ; identityˡ to identityˡᶜ;
  identityʳ to identityʳᶜ; identity² to identity²ᶜ; equiv to equivᶜ;
  ∘-resp-≈ to ∘-resp-≈ᶜ ; ∘-resp-≈ʳ to ∘-resp-≈ʳᶜ ; _⇒_ to _⇒ᶜ_ ;
  _∘_ to _∘ᶜ_ ; Obj to Objᶜ)
  
-- We define natural numbers as an object in our category.
Nat-algebra : Obj
Nat-algebra = record { 
  A = ℕ ; 
  α = α-aux 
  }
  where
    α-aux : 
      (Σ Bool (λ i → (x : A i) → ℕ)) 
      → ℕ
    α-aux (false , f) = 0
    α-aux (true , f) = suc ( f tt )

{-
  We show that this object is an initial F-algebra, so that by
  the Lambek lemma it is then true that 1 + Nat ≅ Nat.
-}
Nat-algebra-initial : Initial P-category
Nat-algebra-initial = record { 
  ⊥ = Nat-algebra ; 
  ⊥-is-initial = record { 
    ! = Nat→B-aux  ; 
    !-unique = Nat→B-unique-aux
    } }

    where
      open F-Algebra Nat-algebra renaming (A to Nat)
      open Functor P

      -- The function to any other object in our category.
      f-aux : {B-alg@record { A = B ; α = β } : F-Algebra P} → 
        Nat ⇒ᶜ B
      f-aux {B-alg = record { A = B ; α = β }} zero = 
        β (false , (λ ()))
      f-aux {B-alg@record { A = B ; α = β }} (suc n) =
        β (true , λ _ → f-aux {B-alg} n)
      
      -- The proof of the commutative diagram that makes it a F-algebra-morphism.
      commutes-aux : {B-alg@record { A = B ; α = β } : F-Algebra P} →
        f-aux {B-alg} ∘ᶜ α
        ≈ᶜ 
        β ∘ᶜ F₁ (f-aux {B-alg})
      commutes-aux {B-alg = record { A = B ; α = β }} {false , f} =
        cong (λ x → β (false , x)) (fun-ext λ x → ⊥-elim x)   
      commutes-aux {B-alg} {true , f} = refl

      -- The morphism to another object.
      Nat→B-aux : {A = B-alg : F-Algebra P} → 
        Nat-algebra ⇒ B-alg
      Nat→B-aux {B-alg} = record { 
        f = f-aux {B-alg} ; 
        commutes = commutes-aux {B-alg} }

      -- Proof of uniqueness that is split by the case of the natural number 
      Nat→B-unique-aux : {A = B-alg : F-Algebra (polynomial-functor A)}
        (f@record {f = f ; commutes = commutes} : F-Algebra-Morphism Nat-algebra B-alg) {x : ℕ} →
        f-aux {B-alg} x ≡ f x
      Nat→B-unique-aux {A = B-alg@record {A = B ; α = β}}
        record { f = f ; commutes = commutes } {zero} =
          begin
            f-aux {B-alg} zero
          ≡⟨ refl ⟩
            f-aux {B-alg} (α ( false , λ ()))
          ≡⟨ cong (λ x → β (false , x)) (fun-ext (λ x → ⊥-elim x)) ⟩
            (β ∘ᶜ (F₁ f)) (false , (λ ()))
          ≡⟨ sym (commutes { false , λ () }) ⟩
            f zero
          ∎
      Nat→B-unique-aux {A = B-alg@record { A = B ; α = β }}
        f-morphism@record { f = f ; commutes = commutes } {suc n} =
        begin
          f-aux {B-alg} (suc n)
        ≡⟨ cong (λ x → β ( true , x )) (fun-ext λ x → Nat→B-unique-aux f-morphism) ⟩
          β (true , λ _ → f n)
        ≡⟨ sym commutes ⟩
          f (suc n)
        ∎
