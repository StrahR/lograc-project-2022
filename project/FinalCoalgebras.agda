module FinalCoalgebras where 

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to Id)

open Definitions using (CommutativeSquare)
open import Coalgebras

private
   variable
      o l e : Level

record FinalCoalgebra {C : Category o l e} (F : Endofunctor C) : Set (o ⊔ l ⊔ e) where 
   eta-equality
   module C = Category C
   open Functor F
   open module CC = Category (CoalgCat F)
   open Coalgebra
   field
      Z : Coalgebra F
      ! : {A : Coalgebra F} → (A ⇒ Z)
      !-unique : ∀ {A} → (f : A ⇒ Z) → ! ≈ f
   open Coalgebra Z public

   !-unique₂ : ∀ {A : Coalgebra F} {f g : A ⇒ Z} → f ≈ g
   !-unique₂ {A} {f} {g} = begin
      f ≈˘⟨ !-unique f ⟩
      ! ≈⟨  !-unique g ⟩
      g ∎
      where open HomReasoning
   
   automf-id : (f : Z ⇒ Z) → f ≈ id
   automf-id f = !-unique₂ {Z} {f} {id}
