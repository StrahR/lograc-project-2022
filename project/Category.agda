module Category where

open import Level using (_⊔_; suc; Level)
-- open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong) -- ≡ is equiv 
-- open import Function using (id; _∘_)

record Category o l : Set (suc (l ⊔ o)) where
    infixl 20 _⇒_ 
    field
        Obj : Set o
        _⇒_ : (A B : Obj) → Set l


        id : (A : Obj) → A ⇒ A
        _∘_ : {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C -- do we need ∀ ???

        lefid : {A B : Obj} → (f : A ⇒ B) → (id B) ∘ f ≡ f
        rightid : {A B : Obj} → (f : A ⇒ B) → f ∘ (id A) ≡ f

        asoc : {A B C D : Obj} → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
        -- left-id : (x : Obj) -> (idm x) ∘ 
    
    id²=id : {A : Obj} → (id A) ∘ (id A) ≡ (id A)
    id²=id = rightid (id _)

record Functor {o l o' l' : Level} (C : Category o l) (D : Category o' l') : Set (l ⊔ o ⊔ o' ⊔ l') where
    private module C = Category C -- so we can reference C, otherwise "C is not a sort"
    private module D = Category D
    field
        F-obj : C.Obj → D.Obj
        F-mor : {A B : C.Obj} → A C.⇒ B → (F-obj A) D.⇒ (F-obj B)

        id-map : (A : C.Obj) → F-mor (C.id A) ≡ D.id (F-obj A)
        ∘-map : {X Y Z : C.Obj} → (f : Y C.⇒ Z) → (g : X C.⇒ Y) → F-mor (f C.∘ g) ≡ (F-mor f) D.∘ (F-mor g)


Endofunctor : {o l : Level} → Category o l → Set (o ⊔ l)
Endofunctor C = Functor C C

record Coalgebra {o l : Level} (S : Category o l) (F : Functor S S) : Set (o ⊔ l) where
    private module S = Category S
    private module F = Functor F
    field
        X : S.Obj
        α : X S.⇒ (F.F-obj X)

record Coa-homo {o l : Level} {S : Category o l} {F : Functor S S} (A : Coalgebra S F) (B : Coalgebra S F) : Set (o ⊔ l) where
    private module A = Coalgebra A
    private module B = Coalgebra B
    private module S = Category S
    private module F = Functor F
    field
        f : A.X S.⇒ B.X

        f-commutes : B.α S.∘ f ≡ (F.F-mor f) S.∘ A.α

{- Coalgebra : {o l : Level} (S : Category o l) (F : Endofunctor S) → Category o l
Coalgebra A = {
    Obj = 
}
-}
        
    