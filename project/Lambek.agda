{-# OPTIONS --guardedness #-}

module Lambek where

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂; uncurry)
open import Categories.Functor using (Functor; Endofunctor)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; subst)

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

   M-coalg : Coalgebra P
   M-coalg = record { X = M-type ; α = μ-aux }
      where μ-aux : M-type S.⇒ P₀ M-type
            μ-aux t with force t
            ...        | node i f = i , f
   open Coalgebra M-coalg renaming (X to M; α to μ)

   PM-coalg : Coalgebra P
   PM-coalg = record { X = P₀ M-type ; α = P₁ μ }
   open Coalgebra PM-coalg renaming (X to PM; α to Pμ)

   PM-ext : {x y : PM}
          → (p : proj₁ x ≡ proj₁ y)
          → ((b : B (proj₁ x)) → proj₂ x b ≅ proj₂ y (subst B p b))
          → x ≡ y
   PM-ext {i , f} {.i , g} refl q = cong (i ,_) (fun-ext (λ b → M-ext (q b)))

   Lambek : Σ[ f@record { map = f-map ; comm = f-comm } ∈ Pcat [ PM-coalg , M-coalg ] ]
               ((t :  M) → f-map (μ t) ≡ t)
             × ((x : PM) → μ (f-map x) ≡ x)
   Lambek = record { map  = λ { (i , f) → record { force = node i f} }
                   ; comm = λ { {x} → PM-ext refl (comm-aux-aux {x}) } }
            , (λ t → M-ext (record { force-≅ = to-aux {t} }))
            , (λ _ → refl)
      where to-aux : {t : M} → node (proj₁ (μ t)) (proj₂ (μ t)) ≅' force t
            to-aux {t} with force t
            ...           | node i f = node-≅ refl λ _ → bisim-refl

            comm-aux-aux : { (i , f) : PM} → (b : B i)
                         → record { force = uncurry node (μ (f b)) } ≅ f b
            comm-aux-aux {i , f} b .force-≅
               with force (f b)
            ...   | node k h = node-≅ refl λ _ → bisim-refl
