module CommSqReasoning where 

open import Level using (_⊔_; suc; Level)
open import Categories.Category
-- open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to Id)

open Definitions using (CommutativeSquare)

private
   variable
      o l e : Level

module Reasoning (𝓒 : Category o l e) where
   open Category 𝓒
   open import Categories.Morphism.Reasoning 𝓒
   open import Categories.Morphism.Reasoning 𝓒 using (glue) public
   open HomReasoning
   open Equiv

   -- create a commutative square from an equivalence
   toSquare : ∀ {A B} {f g : A ⇒ B} → f ≈ g → CommutativeSquare 𝓒 f id id g
   toSquare {_} {_} {f} {g} f≈g = begin
         id ∘ f   ≈⟨ identityˡ ⟩
         f        ≈⟨ f≈g ⟩
         g        ≈˘⟨ identityʳ ⟩
         g ∘ id   ∎
      
   transp : {A B C D : Obj} {f : A ⇒ B} {a : A ⇒ C} {b : B ⇒ D} {g : C ⇒ D}
          → CommutativeSquare 𝓒 f a b g → CommutativeSquare 𝓒 a f g b
   transp {f = f} {a} {b} {g} p = sym p

   cong₁ : {A B C D : Obj} {f f' : A ⇒ B} {a : A ⇒ C} {b : B ⇒ D} {g : C ⇒ D}
         → CommutativeSquare 𝓒 f a b g → f' ≈ f → CommutativeSquare 𝓒 f' a b g
   cong₁ {f = f} {f'} {a} {b} {g} sq p = begin
      b ∘ f' ≈⟨ ∘-resp-≈ʳ p ⟩
      b ∘ f  ≈⟨ sq ⟩
      g ∘ a  ∎

   cong₂ : {A B C D : Obj} {f : A ⇒ B} {a a' : A ⇒ C} {b : B ⇒ D} {g : C ⇒ D}
         → CommutativeSquare 𝓒 f a b g → a' ≈ a → CommutativeSquare 𝓒 f a' b g
   cong₂ {f = f} {a} {a'} {b} {g} sq p = begin
      b ∘ f  ≈⟨ sq ⟩
      g ∘ a  ≈⟨ ∘-resp-≈ʳ (sym p) ⟩
      g ∘ a' ∎

   cong₃ : {A B C D : Obj} {f : A ⇒ B} {a : A ⇒ C} {b b' : B ⇒ D} {g : C ⇒ D}
         → CommutativeSquare 𝓒 f a b g → b' ≈ b → CommutativeSquare 𝓒 f a b' g
   cong₃ {f = f} {a} {b} {b'} {g} sq p = begin
      b' ∘ f ≈⟨ ∘-resp-≈ˡ p ⟩
      b  ∘ f ≈⟨ sq ⟩
      g  ∘ a ∎

   cong₄ : {A B C D : Obj} {f : A ⇒ B} {a : A ⇒ C} {b : B ⇒ D} {g g' : C ⇒ D}
         → CommutativeSquare 𝓒 f a b g → g' ≈ g → CommutativeSquare 𝓒 f a b g'
   cong₄ {f = f} {a} {b} {g} {g'} sq p = begin
      b  ∘ f ≈⟨ sq ⟩
      g  ∘ a ≈⟨ ∘-resp-≈ˡ (sym p) ⟩
      g' ∘ a ∎
 