module sample where

open import Level
-- open import Categories.Category using (Category)
-- open import Categories.Functor using (Functor; Endofunctor)

-- Category sprejme o object, l

record Rel (A : Set) (B : Set) : Set where
    constructor _⇒_
    field
        fst : A
        snd : B
import Data.Nat
data X : Set where
    a : X
    b : X
u = Rel { fst = a ; snd = ?}

{-
record Category {n m : Level} (Objects : Set n) (Morphisms : Set Rel) : Set (n ⊔ m) where
    field
        Obj : Obj'
        ⟶ : 

-- lub least upper bound  is ⊔
record F-Coalgebra {o l e} {C : Category o l e} (F : Endofunctor C): Set (o ⊔ l ⊔ e) where
    open Category C
    field
        x : Obj
        α : 
-}