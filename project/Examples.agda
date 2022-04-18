module Examples where

open import Category using (Category)
open import Data.Nat using (ℕ; _≤_; _+_; suc)
open import Level using (Level; zero)
open import Data.Nat.Properties
open import Relation.Binary using (Transitive; TransFlip)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

Poset-ℕ : Category zero zero
Category.Obj Poset-ℕ = ℕ
Category._⇒_ Poset-ℕ = _≤_
Category.id Poset-ℕ ℕ.zero = _≤_.z≤n
Category.id Poset-ℕ (suc A) = _≤_.s≤s (Category.id Poset-ℕ A)
(Poset-ℕ Category.∘ x) x₁ = ≤-trans x₁ x
Category.lefid Poset-ℕ {.ℕ.zero} {B} _≤_.z≤n = refl
Category.lefid Poset-ℕ {.(suc _)} {.(suc _)} (_≤_.s≤s f) = {! ? ≡  _≤_.s≤s f !}
Category.rightid Poset-ℕ = {!   !}
Category.asoc Poset-ℕ = {!   !} 