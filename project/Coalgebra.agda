module Coalgebra where 

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor; id; _∘F_)

open Definitions using (CommutativeSquare)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

record Coalgebra {o l e : Level} {C : Category o l e} (F : Endofunctor C) : Set (o ⊔ l ⊔ e) where 
    eta-equality
    open Category C
    open Functor F
    field
        X : Obj
        α : X ⇒ F₀ X

record Coalg-hom {o l e : Level} {C : Category o l e} {F : Endofunctor C} (A B : Coalgebra F) : Set (o ⊔ l ⊔ e) where
    open Category C
    open Functor F
    open Coalgebra A
    open Coalgebra B renaming (X to Y; α to β)
    field
        f : X ⇒ Y
        comm : CommutativeSquare C f α β (F₁ f) 
