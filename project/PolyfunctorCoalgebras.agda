{-# OPTIONS --guardedness #-}

module PolyfunctorCoalgebras where

open import Level using (_⊔_; suc; Level)
-- open import Category
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map) 
-- open import Categories.Category.CartesianClosed using (CartesianClosed) CCC doesn't have coproducts or something
open import Categories.Functor using (Functor; Endofunctor; _∘F_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

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

   pr₁ : {A : Set o} {B : A → Set o} → Σ[ a ∈ A ] B a → A
   pr₁ (fst , snd) = fst
   pr₂ : {A : Set o} {B : A → Set o} → (x : Σ[ a ∈ A ] B a) → B (pr₁ x)
   pr₂ (fst , snd) = snd
   pr₁₂ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → Σ[ a ∈ A ] B a
   pr₁₂ (fst , snd , trd) = fst , snd
   pr₃ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → C (pr₁ x)
   pr₃ (fst , snd , trd) = trd

   record M-type {I : Set o} (C B : I → Set o) : Set o where
      coinductive
      constructor inf
      field
         root : Σ[ i ∈ I ] C i
         tree : B (pr₁ root) → M-type C B
   open M-type public

   M-map : {I₁ I₂ : Set o} {C₁ B₁ : I₁ → Set o} {C₂ B₂ : I₂ → Set o}
         → (u : Sets o [ I₁ , I₂ ])
         → (c : (i : I₁) → Sets o [ C₁ i , C₂ (u i) ])
         → (b : (i : I₁) → Sets o [ B₁ i , B₂ (u i) ])
         → M-type C₁ B₁ → M-type C₂ B₂
   M-map u c b t .root    = {! map u c (root t) !}
   M-map u c b t .tree bi = {!  !}

   Pt : (t : M-type C B) → P₀ (M-type C B)
   Pt t = pr₁ (root t) , (pr₂ (root t)) , (λ b → tree t b)

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
               { X = M-type C B
               ; α = λ t → pr₁ (root t) , (pr₂ (root t)) , (λ b → tree t b)
               }
            module C = Category Pcat
            !-aux : {A : Coalgebra P} → Pcat [ A , Z-aux ]
            !-aux {A} = record
               { map  = map-aux
               ; comm = refl
               }
               where open Coalgebra A
                     open Coalgebra Z-aux renaming (X to Z; α to ζ)
                     map-aux : Sets o [ X , Z ]
                     -- map-aux x = inf (pr₁₂ (α x)) (λ b → map-aux (pr₃ (α x) b))
                     map-aux x .root   = pr₁₂ (α x)
                     map-aux x .tree b = map-aux (pr₃ (α x) b)

            !-unique-aux : {X : Coalgebra P}
                         → (f : Pcat [ X , Z-aux ])
                         → Pcat [ !-aux ≈ f ]
            !-unique-aux {X} record { map = f-map ; comm = f-comm } {x} =
               {!   !}
               -- begin
               --    !-map x ≡⟨ {!   !} ⟩
               --    -- inf (pr₁₂ (α x)) (λ b → !-map (pr₃ (α x) b)) ≡⟨ {!   !} ⟩
               --    {!   !} ≡⟨ {!   !} ⟩
               --    {!   !} ≡⟨ {!   !} ⟩
               --    f-map x ∎
               where open Coalgebra Z-aux renaming (X to Z; α to ζ)
                     open Coalgebra X
                     open Eq.≡-Reasoning
                     open Coalg-hom !-aux renaming (map to !-map; comm to !-comm)