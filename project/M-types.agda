{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂; uncurry)
open import Categories.Functor using (Functor)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst; subst-subst-sym)

module M-types {o : Level} {I : Set o} (B : I → Set o) where

   mutual

      data M-type' : Set o where
         node : (i : I) → (B i → M-type) → M-type'

      record M-type : Set o where
         coinductive
         field
            force : M-type'

   open M-type public
   open M-type' public

   module Bisimilarity where

      mutual

         data _≅'_ : M-type' → M-type' → Set o where
            node-≅ : {i j : I} → (p : i ≡ j)
                   → {f : B i → M-type}
                   → {g : B j → M-type}
                   → ((b : B i) → f b ≅ g (subst B p b))
                   → node i f ≅' node j g

         record _≅_ (t u : M-type) : Set o where
            coinductive
            field
               force-≅ : force t ≅' force u

      open _≅_ public
      open _≅'_ public

      postulate M-ext : {t u : M-type} → t ≅ u → t ≡ u

      bisim-refl : {t : M-type} → t ≅ t
      bisim-refl {t} .force-≅
         with force t
      ...   | node i f = node-≅ refl λ _ → bisim-refl
      ≡-to-≅ : {t u : M-type} → t ≡ u → t ≅ u
      ≡-to-≅ refl = bisim-refl

      bisim-transʳ : {t u v : M-type} → t ≅ u → u ≡ v → t ≅ v
      bisim-transʳ p refl = p
      bisim-transˡ : {t u v : M-type} → t ≡ u → u ≅ v → t ≅ v
      bisim-transˡ refl p = p
      bisim-trans : {t u v : M-type} → t ≅ u → u ≅ v → t ≅ v
      bisim-trans p q .force-≅ with force-≅ p | force-≅ q
      ...                         | p         | q = bisim-trans-aux p q
         where bisim-trans-aux : {t u v : M-type'} → t ≅' u → u ≅' v → t ≅' v
               bisim-trans-aux (node-≅ refl p) (node-≅ refl q)
                  = node-≅ refl (λ b → bisim-trans (p b) (q b))

      bisim-sym : {t u : M-type} → t ≅ u → u ≅ t
      bisim-sym p .force-≅ with force-≅ p
      ...                     | p = bisim-sym-aux p
         where bisim-sym-aux : {t u : M-type'} → t ≅' u → u ≅' t
               bisim-sym-aux (node-≅ refl p) = node-≅ refl (λ b → bisim-sym (p b))

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

   open Bisimilarity
