{-# OPTIONS --guardedness --with-K #-}

module PolyfunctorCoalgebras-old where

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
open import Polyfunctor renaming (Polyfunctor-simpl to Poly)

module _ {o : Level} {I : Set o} (B : I → Set o) where
   module S = Category (Sets o)
   P : Endofunctor (Sets o)
   P = Poly B
   Pcat : Category (suc o) o o
   Pcat = CoalgCat P
   open Functor P renaming (F₀ to P₀; F₁ to P₁)

   record M-type : Set o where
      coinductive
      -- constructor inf
      field
         root : I
         tree : B root → M-type
   open M-type public

   record _≅_ (t u : M-type) : Set o where
      coinductive
      field
         root-≡ : root t ≡ root u
         tree-≅ : (b : B (root t)) → tree t b ≅ tree u (subst B root-≡ b)

   postulate M-ext : {t u : M-type} → t ≅ u → t ≡ u

   open _≅_ public
   bisim-refl : {t : M-type} → t ≅ t
   bisim-refl .root-≡   = refl
   bisim-refl .tree-≅ b = bisim-refl

   ≡-to-≅ : {t u : M-type} → t ≡ u → t ≅ u
   ≡-to-≅ refl = bisim-refl

   bisim-transʳ : {t u v : M-type} → t ≅ u → u ≡ v → t ≅ v
   bisim-transʳ p refl = p
   bisim-transˡ : {t u v : M-type} → t ≡ u → u ≅ v → t ≅ v
   bisim-transˡ refl p = p
   bisim-trans : {t u v : M-type} → t ≅ u → u ≅ v → t ≅ v
   bisim-trans             p q .root-≡   = trans (root-≡ p) (root-≡ q)
   bisim-trans {t} {u} {v} p q .tree-≅ b =
      bisim-trans
         (tree-≅ p b)
         (bisim-transʳ
            (tree-≅ q (subst B (root-≡ p) b))
            (cong (λ e → tree v e) (subst-subst (root-≡ p))))

   bisim-sym : {t u : M-type} → t ≅ u → u ≅ t
   bisim-sym         p .root-≡   = sym (root-≡ p)
   bisim-sym {t} {u} p .tree-≅ b =
      bisim-sym (bisim-transʳ
            (tree-≅ p (subst B (sym (root-≡ p)) b))
            (cong (λ e → tree u e) (subst-subst-sym (root-≡ p))))

   module ≅-Reasoning where

      infix  3 _∎
      infixr 2 _≅⟨⟩_ step-≅ step-≅̆
      infixr 2 step-≡ step-≡̆
      infix  1 begin_

      begin_ : ∀{x y : M-type} → x ≅ y → x ≅ y
      begin_ x≅y = x≅y

      _≅⟨⟩_ : ∀ (x {y} : M-type) → x ≅ y → x ≅ y
      _ ≅⟨⟩ x≅y = x≅y

      step-≅ : ∀ (x {y z} : M-type) → y ≅ z → x ≅ y → x ≅ z
      step-≅ _ y≅z x≅y = bisim-trans x≅y y≅z

      step-≅̆ : ∀ (x {y z} : M-type) → y ≅ z → y ≅ x → x ≅ z
      step-≅̆ _ y≅z y≅x = bisim-trans (bisim-sym y≅x) y≅z

      _∎ : ∀ (x : M-type) → x ≅ x
      _∎ _ = bisim-refl

      syntax step-≅ x y≅z x≅y = x ≅⟨ x≅y ⟩ y≅z
      syntax step-≅̆ x y≅z y≅x = x ≅̆⟨ y≅x ⟩ y≅z

      step-≡ : ∀ (x {y z} : M-type) → y ≅ z → x ≡ y → x ≅ z
      step-≡ _ y≅z x≡y = bisim-transˡ x≡y y≅z

      step-≡̆ : ∀ (x {y z} : M-type) → y ≅ z → y ≡ x → x ≅ z
      step-≡̆ _ y≅z y≡x = bisim-transˡ (sym y≡x) y≅z

      syntax step-≡ x y≅z x≡y = x ≡⟨ x≡y ⟩ y≅z
      syntax step-≡̆ x y≅z y≡x = x ≡̆⟨ y≡x ⟩ y≅z


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
