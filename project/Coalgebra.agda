module Coalgebra where 

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Categories.Functor

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

record Coalgebra {o l : level} (C : Category o l) (F : Endofunctor C) : Set (o ⊔ l) where 
    private module C = Category C 
    private module F = Endofunctor F
    field
        X : C.Obj
        α : X ⇒ F₀ X
