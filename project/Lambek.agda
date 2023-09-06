{-# OPTIONS --guardedness #-}

module Lambek where

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂; assocˡ)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ-≡; ,-injectiveʳ-UIP)
open import Categories.Functor using (Functor; Endofunctor; _∘F_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app; subst; resp)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst; subst-subst-sym; subst-sym-subst)

open import Categories.Category.Instance.Sets

open import Coalgebras
open import FinalCoalgebras
open import Polyfunctor renaming (Polyfunctor-simpl to Poly)

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

   M-coalg : Coalgebra P
   M-coalg = record { X = M-type ; α = λ t → root t , λ b → tree t b }
   open Coalgebra M-coalg renaming (X to M; α to μ)
   PM-coalg : Coalgebra P
   PM-coalg = record { X = P₀ M-type ; α = P₁ μ }
   open Coalgebra PM-coalg renaming (X to PM; α to Pμ)

   Lemma : {t : M-type} → t ≡ record { root = root t ; tree = tree t }
   Lemma {t} = M-ext (record { root-≡ = refl ; tree-≅ = λ b → bisim-refl })

   PM-ext : {x y : PM}
          → (p : proj₁ x ≡ proj₁ y)
          → ((b : B (proj₁ x)) → proj₂ x b ≅ proj₂ y (subst B p b))
          → x ≡ y
   PM-ext {x , f} {.x , g} refl q = cong (x ,_) (fun-ext (λ b → M-ext (q b)))

   Lambek : Σ[ f ∈ Pcat [ PM-coalg , M-coalg ] ]
               ((t :  M) → Coalg-hom.map f (μ t) ≡ t)
             × ((x : PM) → μ (Coalg-hom.map f x) ≡ x)
   Lambek = record { map = λ x → record { root = proj₁ x ; tree = proj₂ x }
                         ; comm = comm-aux }
            , (λ _ → M-ext (record { root-≡ = refl
                                   ; tree-≅ = λ _ → bisim-refl }))
            , (λ _ → refl)
      where comm-aux : {x : PM}
                     → x ≡ (proj₁ x , (λ b → record { root = root (proj₂ x b)
                                                    ; tree = tree (proj₂ x b) }))
            comm-aux = PM-ext refl (λ _ → record { root-≡ = refl
                                                       ; tree-≅ = λ _ → bisim-refl })
