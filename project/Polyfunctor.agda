module Polyfunctor where

open import Level using (_⊔_; suc; Level)
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Categories.Functor using (Functor; Endofunctor)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

open import Categories.Category.Instance.Sets

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {f g} → Extensionality f g

Polyfunctor : {o : Level} {I : Set o} → (B : I → Set o) → Endofunctor (Sets o)
Polyfunctor {o = o} {I = I} B = record
   { F₀ = λ S → Σ[ i ∈ I ] ((B i) → S)
   ; F₁ = F₁-aux
   ; identity = refl
   ; homomorphism = refl
   ; F-resp-≈ = F-resp-≈-aux
   }
   where open Category (Sets o) 
         F₁-aux : {V : Set o} {S : Set o}
                → Sets o [ V , S ]
                → Sets o [ 
                     Σ[ i ∈ I ] ((B i) → V) ,
                     Σ[ i ∈ I ] ((B i) → S)
                  ]
         F₁-aux f (i , g) = i , (f ∘ g) 

         F-resp-≈-aux : {V : Set o} {S : Set o}
                      → {f g : Sets o [ V , S ]}
                      → Sets o [ f ≈ g ]
                      → Sets o [ F₁-aux f ≈ F₁-aux g ]
         F-resp-≈-aux r {i , _} = cong (i ,_) (fun-ext λ _ → r)

Polyfunctor-simpl : {o : Level} → (C B : Set o) → Endofunctor (Sets o)
Polyfunctor-simpl {o = o} C B = record
   { F₀ = λ S → (C × (B → S))
   ; F₁ = F₁-aux
   ; identity = refl
   ; homomorphism = refl
   ; F-resp-≈ = F-resp-≈-aux
   }
   where open Category (Sets o) 
         F₁-aux : {V : Set o} {S : Set o}
                → Sets o [ V , S ]
                → Sets o [ 
                     (C × (B → V)) ,
                     (C × (B → S))
                  ]
         F₁-aux f (fst , snd) = (fst , f ∘ snd)

         F-resp-≈-aux : {V : Set o} {S : Set o}
                      → {f g : Sets o [ V , S ]}
                      → Sets o [ f ≈ g ]
                      → Sets o [ F₁-aux f ≈ F₁-aux g ]
         F-resp-≈-aux {f} {g} r {fst , _} = cong (fst ,_ ) (fun-ext (λ _ → r)) 
