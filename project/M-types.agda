{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂)
open import Categories.Functor using (Functor)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst; subst-subst-sym)

module M-types {o : Level} {I : Set o} (B : I → Set o) where

   record M-type : Set o where
      coinductive
      field
         root : I
         tree : B root → M-type
   open M-type public

   module Bisimilarity where
      record _≅_ (t u : M-type) : Set o where
         coinductive
         field
            root-≡ : root t ≡ root u
            tree-≅ : (b : B (root t)) → tree t b ≅ tree u (subst B root-≡ b)
      open _≅_ public

      postulate M-ext : {t u : M-type} → t ≅ u → t ≡ u

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

   open Bisimilarity
