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
   PolyfunctorFinalCoalgebra : FinalCoalgebra (Polyfunctor C B)
   PolyfunctorFinalCoalgebra = record
      { Z = record
         { X = Σ[ i ∈ I ] C i
         ; α = λ {(i , cᵢ) → i , (cᵢ , (λ _ → i , cᵢ))}
         }
      ; ! = record
         { map  = {!   !}
         ; comm = {!   !} }
      ; !-unique = λ {record { map = map ; comm = comm }
                   → {!   !}}
      }
 