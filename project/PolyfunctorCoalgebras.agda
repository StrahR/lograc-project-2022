{-# OPTIONS --guardedness #-}

module PolyfunctorCoalgebras where

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Categories.Functor using (Functor; Endofunctor)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; inspect)

open import Categories.Category.Instance.Sets

open import Coalgebras
open import FinalCoalgebras
open import Polyfunctor renaming (Polyfunctor to Poly)

module _ {o : Level} {I : Set o} (B : I → Set o) where

   private
      module S = Category (Sets o)
      P : Endofunctor (Sets o)
      P = Poly B
      Pcat : Category (suc o) o o
      Pcat = CoalgCat P
      open Functor P renaming (F₀ to P₀; F₁ to P₁)

   open import M-types B
   open Bisimilarity

   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = Z-aux
      ; !        = !-aux
      ; !-unique = λ {f} {x} → M-ext (!-unique-aux {f} {x})
      }
      where
         Z-aux : Coalgebra P
         Z-aux = record { X = M-type ; α = μ-aux }
            where μ-aux : M-type S.⇒ P₀ M-type
                  μ-aux t with force t
                  ...        | node i f = i , f

         module _ {{A : Coalgebra P}} where

            open Coalgebra A
            open Coalgebra Z-aux renaming (X to Z; α to ζ)

            !-aux : Pcat [ A , Z-aux ]
            !-aux = record
               { map  = map-aux
               ; comm = refl
               }
               where map-aux : Sets o [ X , Z ]
                     map-aux x .force = node i (λ b → map-aux (f b))
                        where i = proj₁ (α x); f = proj₂ (α x)

            open Coalg-hom !-aux renaming (map to !-map; comm to !-comm)

            module _ { (record { map = f-map ; comm = f-comm }) : Pcat [ A , Z-aux ]} where

               !-unique-aux : {x : X} → !-map x ≅ f-map x
               !-unique-aux {x} .force-≅ = aux
                  where i = proj₁ (α x); g = proj₂ (α x)

                        aux : force (!-map x) ≅' force (f-map x)
                        aux with force (!-map x)
                               | force (f-map x) | inspect force (!-map x) | f-comm {x}
                        ...    | node .i .(λ b → !-map (g b))
                               | node .i .(λ b → f-map (g b)) | Eq.[ refl ] | refl
                           = node-≅ refl (λ b → !-unique-aux {proj₂ (α x) b})
