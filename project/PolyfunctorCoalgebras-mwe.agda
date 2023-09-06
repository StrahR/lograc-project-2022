{-# OPTIONS --guardedness --with-K #-}

module PolyfunctorCoalgebras-mwe where

open import Level using (_⊔_; suc; Level)
-- open import Category
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂; assocˡ)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ-≡; ,-injectiveʳ-UIP)
-- open import Categories.Category.CartesianClosed using (CartesianClosed) CCC doesn't have coproducts or something
open import Categories.Functor using (Functor; Endofunctor; _∘F_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app; subst; resp)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst; subst-subst-sym; subst-sym-subst)
-- import Relation.Binary.HeterogeneousEquality as HEq
-- open HEq using (_≅_) renaming (refl to hrefl; sym to hsym; trans to htrans; cong to hcong)

-- open import Categories.Category.BinaryProducts using (BinaryProducts)

open import Categories.Category.Instance.Sets

open import Coalgebras
open import FinalCoalgebras
open import Polyfunctor renaming (Polyfunctor-simpl-simpl-simpl to Poly)

module _ {o : Level} (B : Set o) where
   private
      module S = Category (Sets o)
      P : Endofunctor (Sets o)
      P = Poly B
      Pcat : Category (suc o) o o
      Pcat = CoalgCat P
      open Functor P renaming (F₀ to P₀; F₁ to P₁)

   record M-type : Set o where
      coinductive
      field
         tree : B → M-type
   open M-type public

   module Bisimilarity where
      record _≅_ (t u : M-type) : Set o where
         coinductive
         field
            tree-≅ : (b : B) → tree t b ≅ tree u b

      open _≅_ public
      postulate M-ext : {t u : M-type} → t ≅ u → t ≡ u

      bisim-refl : {t : M-type} → t ≅ t
      bisim-refl .tree-≅ _ = bisim-refl
      ≡-to-≅ : {t u : M-type} → t ≡ u → t ≅ u
      ≡-to-≅ refl = bisim-refl

      bisim-transʳ : {t u v : M-type} → t ≅ u → u ≡ v → t ≅ v
      bisim-transʳ p refl = p
      bisim-transˡ : {t u v : M-type} → t ≡ u → u ≅ v → t ≅ v
      bisim-transˡ refl p = p
      bisim-trans : {t u v : M-type} → t ≅ u → u ≅ v → t ≅ v
      bisim-trans p q .tree-≅ b = bisim-trans (tree-≅ p b) (tree-≅ q b)
      bisim-sym : {t u : M-type} → t ≅ u → u ≅ t
      bisim-sym p .tree-≅ b = bisim-sym (tree-≅ p b)

      bicong : {A : Set o} (f : A → M-type) → {x y : A} → x ≡ y → f x ≅ f y
      bicong f refl .tree-≅ b = bisim-refl
   open Bisimilarity

   -- {-# NON_TERMINATING #-}
   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = M-coalg
      ; !        = !
      ; !-unique = λ f {x} → M-ext (!-unique-aux f {x}) --!-unique-aux
      }
      where
         M-coalg : Coalgebra P
         M-coalg = record { X = M-type ; α = tree }
         module _ {A : Coalgebra P} where
            open Coalgebra A
            open Coalgebra M-coalg renaming (X to M; α to μ)

            ! : Pcat [ A , M-coalg ]
            ! = record { map  = map-aux ; comm = refl }
               where map-aux : Sets o [ Coalgebra.X A , M-type ]
                     map-aux x .tree b = map-aux (Coalgebra.α A x b)

            open Coalg-hom ! renaming (map to !-map; comm to !-comm)

            !-unique-aux : (f : Pcat [ A , M-coalg ]) → {x : X} → Coalg-hom.map ! x ≅ Coalg-hom.map f x --Pcat [ ! ≈ f ]
            -- !-unique-aux f {x} = M-ext (!-unique-aux-aux f {x})
            !-unique-aux f@record { map = f-map ; comm = f-comm } {x} =
               bisim-trans
                  (!-unique-aux-aux {x})
                  (bisim-sym f-comm-lift)
               where 
                     f-comm-lift : {x : X} → f-map x ≅ record { tree = λ b → f-map (α x b) }
                     f-comm-lift {x} = record { tree-≅ = λ b → bicong ((λ e → e b)) (f-comm {x}) }

                     !-unique-aux-aux : {x : X} → !-map x ≅ record { tree = λ b → f-map (α x b) }
                     !-unique-aux-aux {x} .tree-≅ b = !-unique-aux f {α x b}

   -- open FinalCoalgebra PolyfunctorFinalCoalgebra renaming (Z to M-coalg)
   M-coalg : Coalgebra P
   M-coalg = record { X = M-type ; α = tree }
   PM-coalg : Coalgebra P
   PM-coalg = record { X = P₀ M-type ; α = P₁ tree }
   open Coalgebra M-coalg renaming (X to M; α to μ)
   Lambek : Σ[ f ∈ Pcat [ PM-coalg , M-coalg ] ]
               ((t :    M-type) → Coalg-hom.map f (tree t) ≡ t)
             × ((x : P₀ M-type) → tree (Coalg-hom.map f x) ≡ x)
   Lambek = (record { map = λ x → record { tree = x } ; comm = comm-aux })
         , (λ t → M-ext (record { tree-≅ = λ b → bisim-refl }))
         , (λ x → refl)
         where comm-aux : {x : B → M-type} → x ≡ (λ b → record { tree = tree (x b) })
               comm-aux {x} = fun-ext (λ b → M-ext (record { tree-≅ = λ b → bisim-refl }))

         -- (λ x → record { tree = x })
         --    , (λ t → M-ext (record { tree-≅ = λ b → bisim-refl }))
         --    , (λ x → refl)