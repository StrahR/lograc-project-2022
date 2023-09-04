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

   record _≅_ (t u : M-type) : Set o where
      coinductive
      field
         tree-≅ : (b : B) → tree t b ≅ tree u b

   postulate M-ext : {t u : M-type} → t ≅ u → t ≡ u

   open _≅_ public

   bisim-refl : {t : M-type} → t ≅ t
   bisim-refl .tree-≅ _ = bisim-refl
   ≡-to-≅ : {t u : M-type} → t ≡ u → t ≅ u
   ≡-to-≅ refl = bisim-refl

   bisim-transʳ : {t u v : M-type} → t ≅ u → u ≡ v → t ≅ v
   bisim-transʳ p refl = p
   bisim-transˡ : {t u v : M-type} → t ≡ u → u ≅ v → t ≅ v
   bisim-transˡ refl p = p
   bisim-trans : {t u v : M-type} → t ≅ u → u ≅ v → t ≅ v
   bisim-trans {t} {u} {v} p q .tree-≅ b =
      bisim-trans
         (tree-≅ p b)
         (tree-≅ q b)

   -- {-# NON_TERMINATING #-}
   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = M-coalg
      ; !        = !
      ; !-unique = !-unique-aux
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

            !-unique-aux : (f : Pcat [ A , M-coalg ]) → Pcat [ ! ≈ f ]
            -- !-unique-aux f {x} = M-ext (!-unique-aux-aux f {x})
            !-unique-aux f@record { map = f-map ; comm = f-comm } {x} =
               trans (M-ext (!-unique-aux-aux {x})) (sym f-comm-lift)
               where !-unique-aux-aux : {x : X} → !-map x ≅ record { tree = λ b → f-map (α x b) }
                     !-unique-aux-aux {x} .tree-≅ b =
                        ≡-to-≅ (!-unique-aux f {α x b})

                     f-comm-lift : f-map x ≡ record { tree = λ b → f-map (α x b) }
                     f-comm-lift = M-ext (record { tree-≅ = λ b → ≡-to-≅ (cong (λ e → e b) (f-comm {x})) })
