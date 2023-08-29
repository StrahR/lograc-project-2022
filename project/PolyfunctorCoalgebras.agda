{-# OPTIONS --guardedness #-}

module PolyfunctorCoalgebras where

open import Level using (_⊔_; suc; Level)
-- open import Category
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂; assocˡ)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ)
-- open import Categories.Category.CartesianClosed using (CartesianClosed) CCC doesn't have coproducts or something
open import Categories.Functor using (Functor; Endofunctor; _∘F_)

open import Data.List
  using
  (List
  ; []; _∷_; _∷ʳ_
  ; sum; map; take; reverse; _++_; drop
  )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; resp)

open import Categories.Category.Instance.Sets

open import Coalgebras
open import FinalCoalgebras
open import Polyfunctor
   renaming (Polyfunctor-simpl-simpl to Poly)

module _ {o : Level} (C B : Set o) where
   module S = Category (Sets o)
   P : Endofunctor (Sets o)
   P = Poly C B
   Pcat : Category (suc o) o o
   Pcat = CoalgCat P
   open Functor P renaming (F₀ to P₀; F₁ to P₁)

   pr₁₂ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → Σ[ a ∈ A ] B a
   pr₁₂ (fst , snd , trd) = fst , snd
   pr₃ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → C (proj₁ x)
   pr₃ (fst , snd , trd) = trd

   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = Z-aux
      ; !        = !-aux
      ; !-unique = !-unique-aux
      }
      where open Definitions using (CommutativeSquare)
            open import CommSqReasoning
            Z-aux : Coalgebra P
            Z-aux = record
               { X = List B → C
               ; α = λ f → f [] , λ b σ → f (b ∷ σ)
               }

            !-aux : {A : Coalgebra P} → Pcat [ A , Z-aux ]
            !-aux {A} = record
               { map  = map-aux
               ; comm = refl
               }
               where open Coalgebra A
                     open Coalgebra Z-aux renaming (X to Z; α to ζ)
                     map-aux : Sets o [ X , Z ]
                     map-aux x []      = proj₁ (α x)
                     map-aux x (b ∷ σ) = map-aux (proj₂ (α x) b) σ

            !-unique-aux : {A : Coalgebra P}
                         → (f : Pcat [ A , Z-aux ])
                         → Pcat [ !-aux ≈ f ]
            !-unique-aux {A} record { map = f-map ; comm = f-comm } {x} = fun-ext (!-unique-aux-aux x)
               where open Coalgebra A
                     open Coalgebra Z-aux renaming (X to Z; α to ζ)
                     open Coalg-hom !-aux renaming (map to !-map; comm to !-comm)

                     !-unique-aux-aux : (x : X)
                                      → (σ : List B)
                                      → !-map x σ ≡ f-map x σ
                     !-unique-aux-aux x [] = sym (cong proj₁ f-comm)
                     !-unique-aux-aux x (b ∷ σ) = begin
                        !-map x (b ∷ σ)             ≡⟨⟩
                        !-map (proj₂ (α x) b) σ     ≡⟨ !-unique-aux-aux (proj₂ (α x) b) σ ⟩
                        f-map (proj₂ (α x) b) σ     ≡⟨⟩
                        proj₂ (P₁ f-map (α x)) b σ  ≡˘⟨ cong (λ e → proj₂ e b σ) f-comm ⟩
                        proj₂ (ζ (f-map x)) b σ     ≡⟨⟩
                        f-map x (b ∷ σ)             ∎
                        where open Reasoning (Sets o)
                              open Eq.≡-Reasoning
