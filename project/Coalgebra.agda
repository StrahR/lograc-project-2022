module Coalgebra where 

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to Id)

open Definitions using (CommutativeSquare)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

private
    variable
        o l e : Level

record Coalgebra {C : Category o l e} (F : Endofunctor C) : Set (o ⊔ l) where 
    eta-equality
    open Category C
    open Functor F
    field
        X : Obj
        α : X ⇒ F₀ X

record Coalg-hom {C : Category o l e} {F : Endofunctor C} (A B : Coalgebra F) : Set (l ⊔ e) where
    eta-equality
    open Category C
    open Functor F
    open Coalgebra A
    open Coalgebra B renaming (X to Y; α to β)
    field
        map : X ⇒ Y
        comm : CommutativeSquare C map α β (F₁ map) 

CoalgCat : {C : Category o l e} → (F : Endofunctor C) → Category (o ⊔ l) (l ⊔ e) e
CoalgCat {C = C} F = record
    { Obj  = Coalgebra F
    ; _⇒_ = Coalg-hom
    ; _≈_  = λ f g → {!   !}
    ; id   = record { map = id ; comm = {!  !} }
    ; _∘_  = λ f g → record { map = map f ∘ map g ; comm = {!   !} }
    ; assoc     = {!   !}
    ; sym-assoc = {!   !}
    ; identityˡ = λ {A} {B} {f} → {!   !}
    ; identityʳ = {!   !}
    ; identity² = {!   !}
    ; equiv     = {!   !}
    ; ∘-resp-≈  = {!   !}
    }
    where open Category C
          open Functor F
          open Coalg-hom 