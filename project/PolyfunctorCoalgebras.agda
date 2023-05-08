module PolyfunctorCoalgebras where

open import Level using (_⊔_; suc; Level)
-- open import Category
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_) 
-- open import Categories.Category.CartesianClosed using (CartesianClosed) CCC doesn't have coproducts or something
open import Categories.Functor using (Functor; Endofunctor; _∘F_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

-- open import Categories.Category.BinaryProducts using (BinaryProducts)

open import Categories.Category.Instance.Sets

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {f g} → Extensionality f g

open import Coalgebras
open import FinalCoalgebras
open import Polyfunctor

module _ {o : Level} {I : Set o} (C B : I → Set o) where
   module S = Category (Sets o)
   P : Endofunctor (Sets o)
   P = Polyfunctor C B
   Pcat : Category (suc o) o o
   Pcat = CoalgCat P
   open Functor P
   
   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = Z-aux
      ; !        = !-aux
      ; !-unique = λ {record { map = map ; comm = comm }
                   → {!   !}}
      }
      where
            Z-aux : Coalgebra P
            Z-aux = record
               { X = Σ[ i ∈ I ] C i
               ; α = λ {(i , cᵢ) → i , (cᵢ , (λ _ → i , cᵢ))}
               }
            module C = Category Pcat
            !-aux : {A : Coalgebra P}
                  → Pcat [ A , Z-aux ]
            !-aux {A} = record
               { map  = map-aux
               ; comm = {! comm-aux  !}
               }
               where open Coalgebra A
                     open Coalgebra Z-aux renaming (X to Z; α to ζ)
                     open Functor P renaming (F₀ to P₀; F₁ to P₁)
                     map-aux : Sets o [ X , Z ]
                     map-aux x = (λ (i , c , _) → (i , c)) (α x)
                     
                     comm-aux : {!   !}
                     comm-aux = {!   !}


 