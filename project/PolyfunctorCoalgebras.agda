
module PolyfunctorCoalgebras where

open import Level using (_⊔_; suc; Level)
-- open import Category
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂; assocˡ)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ)
-- open import Categories.Category.CartesianClosed using (CartesianClosed) CCC doesn't have coproducts or something
open import Categories.Functor using (Functor; Endofunctor; _∘F_)

open import Data.List
  using
  (List
  ; []; _∷_
  ; sum; map; take; reverse; _++_; drop
  )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; resp)
-- import Relation.Binary.HeterogeneousEquality as HEq
-- open HEq using (_≅_) renaming (refl to hrefl; sym to hsym; trans to htrans; cong to hcong)

-- open import Categories.Category.BinaryProducts using (BinaryProducts)

open import Categories.Category.Instance.Sets

open import Coalgebras
open import FinalCoalgebras
open import Polyfunctor

module _ {o : Level} {I : Set o} (C B : I → Set o) where
   module S = Category (Sets o)
   P : Endofunctor (Sets o)
   P = Polyfunctor C B
   Pcat : Category (suc o) o o
   Pcat = CoalgCat P
   open Functor P renaming (F₀ to P₀; F₁ to P₁)

   -- data M-type {I : Set o} (C B : I → Set o) : Set (suc o) where
   --    inf : (i : I) → C i × (B i → ∞ (M-type C B)) → M-type C B

   pr₁₂ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → Σ[ a ∈ A ] B a
   pr₁₂ (fst , snd , trd) = fst , snd
   pr₃ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → C (proj₁ x)
   pr₃ (fst , snd , trd) = trd


   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = Z-aux
      ; !        = !-aux
      ; !-unique = !-unique-aux
      }
      where open Definitions using (CommutativeSquare)
            open import CommSqReasoning
            Z-aux : Coalgebra P
            Z-aux = record 
            { X = List (Σ [ i ∈ I ] B i) → Σ [ i ∈ I ] C i
            ; α = 
            }