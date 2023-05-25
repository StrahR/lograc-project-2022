{-# OPTIONS --guardedness --with-K #-}

module PolyfunctorCoalgebras where

open import Level using (_⊔_; suc; Level)
-- open import Category
open import Categories.Category
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; map; proj₁; proj₂; assocˡ)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ)
-- open import Categories.Category.CartesianClosed using (CartesianClosed) CCC doesn't have coproducts or something
open import Categories.Functor using (Functor; Endofunctor; _∘F_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; resp)
-- import Relation.Binary.HeterogeneousEquality as HEq
-- open HEq using (_≅_) renaming (refl to hrefl; sym to hsym; trans to htrans; cong to hcong)

-- open import Categories.Category.BinaryProducts using (BinaryProducts)

open import Categories.Category.Instance.Sets

open import Coalgebras
open import FinalCoalgebras
open import Polyfunctor

module _ {o : Level} {I : Set o} (C B : I → Set o) where
   module S = Category (Sets o)
   P : Endofunctor (Sets o)
   P = Polyfunctor C B
   Pcat : Category (suc o) o o
   Pcat = CoalgCat P
   open Functor P renaming (F₀ to P₀; F₁ to P₁)

   -- data M-type {I : Set o} (C B : I → Set o) : Set (suc o) where
   --    inf : (i : I) → C i × (B i → ∞ (M-type C B)) → M-type C B

   pr₁₂ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → Σ[ a ∈ A ] B a
   pr₁₂ (fst , snd , trd) = fst , snd
   pr₃ : {A : Set o} {B C : A → Set o} → (x : Σ[ a ∈ A ] B a × C a) → C (proj₁ x)
   pr₃ (fst , snd , trd) = trd

   record M-type {I : Set o} (C B : I → Set o) : Set o where
      -- eta-equality
      coinductive
      constructor inf
      field
         root : Σ[ i ∈ I ] C i
         tree : B (proj₁ root) → M-type C B
   open M-type public

   -- Can't define this without preimages of b
   -- M-map : {I₁ I₂ : Set o} {C₁ B₁ : I₁ → Set o} {C₂ B₂ : I₂ → Set o}
   --       → (u : Sets o [ I₁ , I₂ ])
   --       → (c : (i : I₁) → Sets o [ C₁ i , C₂ (u i) ])
   --       → (b : (i : I₁) → Sets o [ B₁ i , B₂ (u i) ])
   --       → M-type C₁ B₁ → M-type C₂ B₂
   -- M-map u c b t .root    = (u i) , (c i ci)
   --    where i  = proj₁ (root t)
   --          ci = proj₂ (root t)
   -- M-map u c b t .tree bi = M-map u c b {!  tree t  !}
   --    where i  = proj₁ (root t)
   --          ci = proj₂ (root t)
   --          b' = proj₁ (Σ[ b' ∈ B₁ i ] b b' ≡ )

   record _≅_ {I : Set o} {C B : I → Set o} (t u : M-type C B) : Set o where
      coinductive
      constructor bisim
      field
         root-≡ : root t ≡ root u
         tree-≅ : (b : B (proj₁ (root t))) → tree t b ≅ tree u (resp B (cong proj₁ root-≡) b)

   resp²≡refl : {A : Set o} {B : A → Set o} {a a' : A}
              → (p : a ≡ a') → {b : B a}
              → resp B (sym p) (resp B p b) ≡ b
   resp²≡refl refl = refl
   resp²≡refl₂ : {I : Set o} {C B : I → Set o} {a a' : Σ[ i ∈ I ] C i}
               → (p : a ≡ a') → {b : B (proj₁ a)}
               → resp B (cong proj₁ (sym p)) (resp B (cong proj₁ p) b) ≡ b
   resp²≡refl₂ refl = refl

   postulate
      M-ext : {t u : M-type C B}
            → t ≅ u
            -- → (p : root t ≡ root u)
            -- → ((b : B (proj₁ (root t))) → tree t b ≡ tree u (resp B (cong proj₁ p) b))
            -- → tree t ≅ tree u
            → t ≡ u
   -- M-ext p q = {!   !}

   -- Pt : (i : I) → (t : M-type i (C i) (B i)) → P₀ (M-type i (C i) (B i))
   -- Pt i t = i , root t , tree t
                     
                     -- M-ext : root (!-map x) ≡ root (f-map x)
                     --       → tree (!-map x) ≡ tree (f-map x)
                     --       → !-map x ≡ f-map x
                     -- M-ext p q = {!   !}
   Pt : (t : M-type C B) → P₀ (M-type C B)
   Pt t = proj₁ (root t) , (proj₂ (root t)) , (λ b → tree t b)

   PolyfunctorFinalCoalgebra : FinalCoalgebra P
   PolyfunctorFinalCoalgebra = record
      { Z        = Z-aux
      ; !        = !-aux
      ; !-unique = !-unique-aux
      }
      where open Definitions using (CommutativeSquare)
            open import CommSqReasoning
            Z-aux : Coalgebra P
            Z-aux = record
               { X = M-type C B
               ; α = λ t → proj₁ (root t) , (proj₂ (root t)) , (λ b → tree t b)
               }
            module C = Category Pcat
            !-aux : {A : Coalgebra P} → Pcat [ A , Z-aux ]
            !-aux {A} = record
               { map  = map-aux
               ; comm = refl
               }
               where open Coalgebra A
                     open Coalgebra Z-aux renaming (X to Z; α to ζ)
                     map-aux : Sets o [ X , Z ]
                     -- map-aux x = inf (pr₁₂ (α x)) (λ b → map-aux (pr₃ (α x) b))
                     -- map-aux x .root   = pr₁₂ (α x)
                     map-aux x .root   = proj₁ (α x) , proj₁ (proj₂ (α x))
                     map-aux x .tree b = map-aux (pr₃ (α x) b)

            !-unique-aux : {Xalg : Coalgebra P}
                         → (f : Pcat [ Xalg , Z-aux ])
                        --  → (x : Coalgebra.X Xalg)
                         → Pcat [ !-aux ≈ f ]
            !-unique-aux {Xalg} record { map = f-map ; comm = f-comm } {x} =
               -- {!   !}
               M-ext (bisim root-aux tree-aux)
               -- begin
               --    !-map x ≡⟨ {!   !} ⟩
               --    -- inf (pr₁₂ (α x)) (λ b → !-map (pr₃ (α x) b)) ≡⟨ {!   !} ⟩
               --    {!   !} ≡⟨ {!   !} ⟩
               --    {!   !} ≡⟨ {!   !} ⟩
               --    f-map x ∎
               where open Coalgebra Z-aux renaming (X to Z; α to ζ)
                     open Coalgebra Xalg
                     open Coalg-hom (!-aux {Xalg}) renaming (map to !-map; comm to !-comm)

                     f : Pcat [ Xalg , Z-aux ]
                     f = record { map = f-map ; comm = f-comm }

                     lemma : Pcat [ !-aux ≈ f ]
                           → Coalg-hom.map (!-aux {Xalg}) ≡ Coalg-hom.map f
                     lemma p = fun-ext λ x → p

                     root-aux : root (!-map x) ≡ root (f-map x)
                     root-aux = --{!   !}
                        begin
                        root (!-map x)   ≡⟨ refl ⟩
                        pr₁₂ (α x)      ≡˘⟨ ,-injectiveˡ (cong assocˡ f-comm) ⟩
                        root (f-map x) ∎
                        where open Reasoning (Sets o)
                              open Eq.≡-Reasoning

                     -- root-aux-aux-aux : proj₁ (α x) ≡ proj₁ (root (!-map x))
                     -- root-aux-aux-aux = begin
                     --    proj₁ (root (!-map x)) ≡⟨ refl ⟩
                     --    proj₁ (pr₁₂ (α x))     ≡⟨ refl ⟩
                     --    proj₁ (α x)            ∎
                     --    where open Eq.≡-Reasoning

                     tree-aux : (b : B (proj₁ (root (!-map x))))
                              → tree (!-map x) b ≅ tree (f-map x) (resp B (cong proj₁ root-aux) b)
                     tree-aux b = {!  ? !}
                     -- begin
                     --    tree (!-map x) b                            ≡⟨ refl ⟩
                     --    -- !-map (pr₃ (α x) b)                         ≡⟨ !-unique-aux f {(pr₃ (α x) b)} ⟩
                     --    !-map (pr₃ (α x) b)                         ≡⟨ lemma₂ ⟩
                     --    -- !-map (pr₃ (α x) b)                         ≡⟨ refl ⟩
                     --    -- pr₃ (P₁ !-map (α x)) b                      ≡⟨ cong (λ fun → pr₃ (P₁ fun (α x)) b) (lemma (!-unique-aux f)) ⟩
                     --    -- !-map (pr₃ (α x) b)                         ≡⟨ sym M-eta ⟩
                     --    -- inf
                     --    --    (pr₁₂ (α (pr₃ (α x) b)))
                     --    --    (λ b′ → !-map (pr₃ (α (pr₃ (α x) b)) b′)) ≡⟨ M-ext tree-root-aux tree-tree-aux ⟩
                     --    -- inf
                     --    --    (root (pr₃ (P₁ f-map (α x)) b''))
                     --    --    (tree (pr₃ (P₁ f-map (α x)) b''))        ≡⟨ M-eta ⟩
                     --    f-map (pr₃ (α x) b)                         ≡⟨ refl ⟩
                     --    pr₃ (P₁ f-map (α x)) b                      ≡⟨ f-comm-aux ⟩
                     --    pr₃ (ζ (f-map x)) b'                        ≡⟨ refl ⟩
                     --    tree (f-map x) b'                           ∎
                     -- -- tree-aux = begin
                     -- --    tree (!-map x) ≅⟨ hrefl ⟩
                     -- --    (λ b → !-map (proj₂ (proj₂ (α x)) b)) ≅⟨ {!   !} ⟩
                     -- --    {!   !}       ≅⟨ {!   !} ⟩
                     -- --    {!   !}       ≅⟨ {!   !} ⟩
                     -- --    proj₂ (proj₂ (P₁ f-map (α x))) ≅˘⟨ hcong (λ y → proj₂ (proj₂ y)) (HEq.≡-to-≅ root-aux-aux) ⟩
                     -- --    proj₂ (proj₂ (ζ (f-map x)))    ≅⟨ hrefl ⟩
                     -- --    proj₂ (proj₂ ((λ t → proj₁ (root t) , (proj₂ (root t) , tree t)) (f-map x)))    ≅⟨ hrefl ⟩
                     -- --    -- proj₂ (proj₂ (proj₁ (root (f-map x)) , proj₂ (root (f-map x)) , tree (f-map x)))   ≅⟨ {!   !} ⟩
                     -- --    tree (f-map x) ∎
                        where open Eq.≡-Reasoning
                              b'  = resp B (cong proj₁      root-aux)  b
                              b'' = resp B (sym (cong proj₁ root-aux)) b'

                              b=b'' : b ≡ b''
                              b=b'' = begin
                                 b 
                                    ≡˘⟨ resp²≡refl₂ {B = B} root-aux ⟩
                                 -- resp B (sym (cong proj₁ root-aux)) (resp B (cong proj₁ root-aux) b)
                                    -- ≡⟨ ? ⟩
                                 resp B (cong proj₁ (sym root-aux)) (resp B (cong proj₁ root-aux) b)
                                    ≡⟨ refl ⟩
                                 resp B (cong proj₁ (sym root-aux)) b'
                                    ≡⟨ {!   !} ⟩
                                 b'' ∎

                              -- postulate
                              --    M-eta : {t : M-type C B} → inf (root t) (tree t) ≡ t
                              --    f-comm-aux : pr₃ (P₁ f-map (α x)) b ≡ pr₃ (ζ (f-map x)) b'

                              -- zfx = ζ (f-map x)
                              -- pfax = P₁ f-map (α x)
                              -- root-aux-aux : zfx ≡ pfax
                              -- root-aux-aux = f-comm

                              lemma₂ : !-map (pr₃ (α x) b) ≡ f-map (pr₃ (α x) b)
                              lemma₂ with (pr₃ (α x) b)
                              ...         | p = {!   !}

                              -- tree-root-aux : pr₁₂ (α (pr₃ (α x) b)) ≡ root (pr₃ (P₁ f-map (α x)) b'')
                              -- tree-root-aux = {!   !}

                              -- tree-tree-aux : (b′ : B (proj₁ (α (pr₃ (α x) b))))
                              --               → !-map (pr₃ (α (pr₃ (α x) b)) b′)
                              --               ≡ tree (pr₃ (P₁ f-map (α x)) b'') (resp B (cong proj₁ tree-root-aux) b′)
                              -- tree-tree-aux b′ = {!   !}
                              --    where b′′ = resp B (cong proj₁ tree-root-aux) b′

                     -- M-ext : root (!-map x) ≡ root (f-map x)
                     --       → tree (!-map x) ≡ tree (f-map x)
                     --       → !-map x ≡ f-map x
                     -- M-ext p q = {!   !}