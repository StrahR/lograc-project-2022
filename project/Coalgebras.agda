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
         map : X ⇒ Y
         comm : CommutativeSquare C map α β (F₁ map)

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
                        → CommutativeSquare C id→ (α A) (α A) (F₁ id→)
            id-comm-aux = cong₄ (toSquareᵥ refl) identity
            
            ∘-comm-aux : {K L M : Coalgebra F}
                     → (f : Coalg-hom L M) → (g : Coalg-hom K L)
                     → CommutativeSquare C (map f ∘ map g) (α K) (α M) (F₁ (map f ∘ map g))
            ∘-comm-aux f g = cong₄ (glueₕ (comm f) (comm g)) homomorphism
