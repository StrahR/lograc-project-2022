{-# OPTIONS --guardedness --with-K #-}

module PolyfunctorCoalgebras-old where

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂; assocˡ)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ-≡; ,-injectiveʳ-UIP)
open import Categories.Functor using (Functor; Endofunctor)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app; subst; resp)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst; subst-subst-sym)

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

   -- {-# NON_TERMINATING #-}
   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = Z-aux
      ; !        = !-aux
      ; !-unique = !-unique-aux
      }
      where 
         Z-aux : Coalgebra P
         Z-aux = record
            { X = M-type
            ; α = λ t → root t , λ b → tree t b
            }
            
         module _ {A : Coalgebra P} where
            open Coalgebra A
            open Coalgebra Z-aux renaming (X to Z; α to ζ)

            !-aux : Pcat [ A , Z-aux ]
            !-aux = record
               { map  = map-aux
               ; comm = refl
               }
               where map-aux : Sets o [ X , Z ]
                     map-aux x .root   = proj₁ (α x)
                     map-aux x .tree b = map-aux (proj₂ (α x) b)

            open Coalg-hom !-aux renaming (map to !-map; comm to !-comm)

            !-unique-aux-aux : (f : Pcat [ A , Z-aux ]) → {x : X}  → !-map x ≅ Coalg-hom.map f x
            !-unique-aux-aux f@record { map = f-map ; comm = f-comm } {x} =
               record { root-≡ = root-aux
                      ; tree-≅ = tree-aux {x}
                      }
               where root-aux : {x : X} → root (!-map x) ≡ root (f-map x)
                     root-aux = sym (cong proj₁ f-comm)

                     tree-aux : {x : X} → (b : B (root (!-map x)))
                              → tree (!-map x) b ≅ tree (f-map x) (subst B root-aux b)
                     tree-aux {x} b = bisim-trans
                        (!-unique-aux-aux f {proj₂ (α x) b})
                        {!   !}
                     -- begin
                     --    tree (!-map x) b      ≅⟨⟩
                     --    !-map (proj₂ (α x) b) ≅⟨ !-unique-aux-aux {proj₂ (α x) b} ⟩
                     --    f-map (proj₂ (α x) b) ≡̆⟨ cong (λ e → f-map (proj₂ (α x) e)) subst-lemma ⟩
                     --    proj₂ (P₁ f-map (α x)) (subst B (cong proj₁ f-comm) (subst B root-aux b))
                     --       -- ≡̆⟨ cong-app (,-injectiveʳ-≡ {!   !} f-comm (cong proj₁ (f-comm {x}))) {!   !} ⟩
                     --       ≡̆⟨ cong proj₂ f-comm-lemma  ⟩
                     --       -- ≡̆⟨ {!  (,-injectiveʳ-≡ ? f-comm (cong proj₁ (f-comm {x})))  !} ⟩
                     --    proj₂ (ζ (f-map x)) (subst B root-aux b) ≅⟨⟩
                     --    tree (f-map x) (subst B root-aux b) ∎
                     --    where open ≅-Reasoning

                     --          subst-lemma : subst B (cong proj₁ f-comm) (subst B root-aux b) ≡ b
                     --          subst-lemma = subst-sym-subst (cong proj₁ f-comm)
                     --          postulate
                     --             f-comm-lemma :
                     --                (root (f-map x) , tree (f-map x) (subst B root-aux b))
                     --                ≡ (proj₁ (α x) , f-map (proj₂ (α x)  (subst B (cong (λ r → proj₁ r) f-comm) (subst B root-aux b))))
                     --          -- f-comm-lemma = cong proj₂ {! f-comm  !}

            !-unique-aux : (f : Pcat [ A , Z-aux ]) → Pcat [ !-aux ≈ f ]
            !-unique-aux f {x} = M-ext (!-unique-aux-aux f {x})
