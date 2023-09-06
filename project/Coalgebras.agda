module Coalgebras where 

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to Id)

open Definitions using (CommutativeSquare)

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; sym; trans; cong)

private
   variable
      o l e : Level

module _ {C : Category o l e} where
   record Coalgebra (F : Endofunctor C) : Set (o ⊔ l) where 
      eta-equality
      open Category C
      open Functor F
      field
         X : Obj
         α : X ⇒ F₀ X

   record Coalg-hom {F : Endofunctor C} (A B : Coalgebra F) : Set (l ⊔ e) where
      eta-equality
      open Category C
      open Functor F
      open Coalgebra A
      open Coalgebra B renaming (X to Y; α to β)
      field
         map  : X ⇒ Y
         comm : CommutativeSquare C α map (F₁ map) β

   CoalgCat : (F : Endofunctor C) → Category (o ⊔ l) (l ⊔ e) e
   CoalgCat F = record
      { Obj  = Coalgebra F
      ; _⇒_ = Coalg-hom
      ; _≈_  = λ f g → map f ≈ map g
      ; id   = record { map = id→ ; comm = id-comm-aux }
      ; _∘_  = λ f g → record { map = map f ∘ map g ; comm = ∘-comm-aux f g }
      ; assoc     = assoc
      ; sym-assoc = sym-assoc
      ; identityˡ = identityˡ
      ; identityʳ = identityʳ
      ; identity² = identity²
      ; equiv     = record { refl = refl ; sym = sym ; trans = trans }
      ; ∘-resp-≈  = ∘-resp-≈
      }
      where open Category C renaming (id to id→)
            open Functor F
            open Coalgebra
            open Coalg-hom
            open Equiv
            open import CommSqReasoning
            open Reasoning C

            id-comm-aux : {A : Coalgebra F}
                        → CommutativeSquare C (α A) id→ (F₁ id→) (α A)
            id-comm-aux {A} = cong₃ (toSquareₕ refl) identity

            ∘-comm-aux : {K L M : Coalgebra F}
                     → (f : Coalg-hom L M) → (g : Coalg-hom K L)
                     → CommutativeSquare C (α K) (map f ∘ map g) (F₁ (map f ∘ map g)) (α M)
            ∘-comm-aux f g = cong₃ (glueᵥ (comm f) (comm g)) homomorphism
 