module Polyfunctor where

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

private
   variable
      o l e : Level



Polyfunctor : {I : Set o} → (C : I → Set o) → (B : I → Set o) → Endofunctor ({! !})
Polyfunctor {I = I} C B = record
   { F₀ = λ S → Σ[ i ∈ I ] ((B i) → S) -- full definition would have (C i) x ...
   ; F₁ = F₁-aux
   ; identity = refl
   ; homomorphism = refl
   ; F-resp-≈ = {!   !}
   }
   where open Category (Sets {!   !})
--         open Sets ? I

         F₁-aux : {B = V : Set {!  !}} {S : Set {! o  !}} →
           Sets {!   !} [ V , S ] → 
           Sets {!   !} [ 
             Σ[ i ∈ I ] (B i → V) , 
             Σ[ i ∈ I ] (B i → S)
             ]
         F₁-aux f (i , g) = i , (f ∘ g)
           