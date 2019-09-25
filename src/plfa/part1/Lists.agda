module plfa.part1.Lists where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; sym; trans; cong)
    open Eq.≡-Reasoning
    open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
    open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
    open import Relation.Nullary using (¬_; Dec; yes; no)
    open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Function using (_∘_)
    open import Level using (Level)
    open import plfa.part1.Isomorphism using (_≃_; _⇔_)

    data List (A : Set) : Set where
        []   : List A
        _∷_ :  A → List A → List A

    infixr 5 _∷_
    {-# BUILTIN LIST List #-}

    pattern [_] z = z ∷ []
    pattern [_,_] y z = y ∷ z ∷ []
    pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
    pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
    pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
    pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []    

    infixr 5 _++_

    _++_ : ∀ {A : Set} → List A → List A → List A
    []       ++ ys  =  ys
    (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

    -- List Reasoning
    ++-assoc : ∀ {A : Set} (xs ys zs : List A)
                        → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs = 
        begin
            ([] ++ ys) ++ zs
            ≡⟨⟩
            ys ++ zs
            ≡⟨⟩
            [] ++ (ys ++ zs)
        ∎
    
    ++-assoc (x ∷ xs) ys zs = 
        begin
            (x ∷ xs ++ ys) ++ zs
            ≡⟨⟩
            x ∷ ((xs ++ ys) ++ zs)
            ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
            x ∷ (xs ++ (ys ++ zs))
            ≡⟨⟩
            x ∷ xs ++ (ys ++ zs)
        ∎

    ++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
    ++-identityˡ xs = refl

    ++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
    ++-identityʳ [] = refl
    ++-identityʳ (x ∷ xs) = 
        begin
            x ∷ xs ++ []
            ≡⟨⟩
            x ∷ (xs ++ [])
            ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
            x ∷ xs
        ∎

    -- Length & Reasoning
    length : ∀ {A : Set} → List A → ℕ
    length []        =  zero
    length (x ∷ xs)  =  suc (length xs)

    length-++ : ∀ {A : Set} (xs ys : List A)
                            → length (xs ++ ys) ≡ length xs + length ys
    length-++ [] ys = refl
    length-++ (x ∷ xs) ys = 
        begin
            length (x ∷ xs ++ ys)
            ≡⟨⟩
            length (x ∷ (xs ++ ys))
            ≡⟨⟩
            suc (length (xs ++ ys))
            ≡⟨ cong suc (length-++ xs ys) ⟩
            suc (length xs + length ys)
            ≡⟨⟩
            length (x ∷ xs) + length (ys)
        ∎
    
    -- Reverse
    reverse : ∀ {A : Set} → List A → List A
    reverse []        =  []
    reverse (x ∷ xs)  =  reverse xs ++ [ x ]

    -- Exercise reverse-++-commute
    -- reverse-++-commute {xs = xs} {ys = []} =
        -- begin
        --     reverse (xs ++ [])
        --     ≡⟨ cong reverse (++-identityʳ xs) ⟩
        --     reverse xs
        --     ≡⟨⟩
        --     [] ++ (reverse xs)
        -- ∎
    ++-lem : ∀ {A : Set} → (xs : List A) → xs ≡ xs ++ []
    ++-lem [] = refl
    ++-lem (x ∷ xs) = cong (x ∷_) (++-lem xs)

    reverse-inv : ∀ {A : Set} → (x : A) → (xs : List A) → reverse xs ++ [ x ] ≡ reverse (x ∷ xs)
    reverse-inv _ _ = refl


    -- Name change / explicit param suggested by ice1k.
    reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
                            → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
    reverse-++-distrib [] ys =
        begin
            reverse ([] ++ ys)
            ≡⟨⟩
            reverse ys
            ≡⟨ ++-lem (reverse ys) ⟩
            (reverse ys) ++ []
            ≡⟨⟩
            reverse ys ++ reverse []
        ∎
    reverse-++-distrib (x ∷ xs) ys = 
        begin
            reverse (x ∷ xs ++ ys)
            ≡⟨⟩
            reverse (x ∷ (xs ++ ys))
            ≡⟨⟩
            reverse (xs ++ ys) ++ [ x ]
            ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
            (reverse ys ++ reverse xs) ++ [ x ]
            ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
            reverse ys ++ (reverse xs ++ [ x ])
            ≡⟨ cong ((reverse ys) ++_) (reverse-inv x xs) ⟩
            reverse ys ++ reverse (x ∷ xs)
        ∎

    reverse-++-commute : ∀ {A : Set} {xs ys : List A}
                            → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
    reverse-++-commute {xs = []} {ys = ys} =
        begin
            reverse ([] ++ ys)
            ≡⟨⟩
            reverse ys
            ≡⟨ ++-lem (reverse ys) ⟩
            (reverse ys) ++ []
            ≡⟨⟩
            reverse ys ++ reverse []
        ∎
    reverse-++-commute {xs = x ∷ xs}{ys = ys} = 
        begin
            reverse (x ∷ xs ++ ys)
            ≡⟨⟩
            reverse (x ∷ (xs ++ ys))
            ≡⟨⟩
            reverse (xs ++ ys) ++ [ x ]
            ≡⟨ cong (_++ [ x ]) (reverse-++-commute {xs = xs} {ys = ys}) ⟩
            (reverse ys ++ reverse xs) ++ [ x ]
            ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
            reverse ys ++ (reverse xs ++ [ x ])
            ≡⟨ cong ((reverse ys) ++_) (reverse-inv x xs) ⟩
            reverse ys ++ reverse (x ∷ xs)
        ∎

    reverse-involutive : ∀ {A : Set} {xs : List A} → reverse (reverse xs) ≡ xs
    reverse-involutive {xs = []} = refl
    reverse-involutive {xs = x ∷ xs} = 
        begin
            reverse (reverse (x ∷ xs))
            ≡⟨⟩
            reverse ((reverse xs) ++ [ x ])
            ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
            reverse [ x ] ++ reverse (reverse xs)
            ≡⟨⟩
            [ x ] ++ reverse (reverse xs)
            ≡⟨ cong ([ x ] ++_) (reverse-involutive {xs = xs}) ⟩
            [ x ] ++ xs
            ≡⟨⟩
            x ∷ xs
        ∎
    
    -- Fast reverse
    shunt : ∀ {A : Set} → List A → List A → List A
    shunt []       ys  =  ys
    shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

    shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
    shunt-reverse [] ys = refl
    shunt-reverse (x ∷ xs) ys =
        begin
            shunt (x ∷ xs) ys
            ≡⟨⟩
            shunt xs (x ∷ ys)
            ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
            reverse xs ++ (x ∷ ys)
            ≡⟨⟩
            reverse xs ++ ([ x ] ++ ys)
            ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
            (reverse xs ++ [ x ]) ++ ys
            ≡⟨⟩
            reverse (x ∷ xs) ++ ys
        ∎
    
    reverse′ : ∀ {A : Set} → List A → List A
    reverse′ xs = shunt xs []

    reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
    reverses xs =
        begin
            reverse′ xs
            ≡⟨⟩
                shunt xs []
            ≡⟨ shunt-reverse xs [] ⟩
                reverse xs ++ []
            ≡⟨ ++-identityʳ (reverse xs) ⟩
                reverse xs
        ∎
    
    -- Map
    map : ∀ {A B : Set} → (A → B) → List A → List B
    map f []        =  []
    map f (x ∷ xs)  =  f x ∷ map f xs

    sucs : List ℕ → List ℕ
    sucs = map suc

    -- Practice map-compose
    map-comp-lem : {A B C : Set}{f : A → B}{g : B → C} → ∀ (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    map-comp-lem [] = refl
    map-comp-lem {f = f}{g = g}(x ∷ xs) = 
        begin
            map (g ∘ f) (x ∷ xs)
            ≡⟨⟩
            ((g ∘ f) x) ∷ map (g ∘ f) xs
            ≡⟨ cong (((g ∘ f) x) ∷_) (map-comp-lem xs) ⟩
            ((g ∘ f) x) ∷ (map g ∘ map f) xs
            ≡⟨⟩
            (map g ∘ map f) (x ∷ xs)
        ∎

    map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C} → map (g ∘ f) ≡ map g ∘ map f
    map-compose = plfa.part1.Isomorphism.extensionality (map-comp-lem)

    -- Exercise map-++-commute
    map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A} → map f (xs ++ ys) ≡ map f xs ++ map f ys
    map-++-commute {xs = []}{ys = ys} = refl
    map-++-commute {f = f}{xs = x ∷ xs}{ys = ys} = 
        begin
            map f (x ∷ xs ++ ys)
            ≡⟨⟩
            f x ∷ map f (xs ++ ys)
            ≡⟨ cong ((f x) ∷_) (map-++-commute {xs = xs} {ys = ys}) ⟩
            f x ∷ (map f xs ++ map f ys)
            ≡⟨⟩
            map f (x ∷ xs) ++ map f ys
        ∎
    
    -- Practice map-tree
    data Tree (A B : Set) : Set where
        leaf : A → Tree A B
        node : Tree A B → B → Tree A B → Tree A B
    
    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
    map-Tree f g (leaf x) = leaf (f x)
    map-Tree f g (node t1 v t2) = node (map-Tree f g t1) (g v) (map-Tree f g t2)

    -- Fold
    foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
    foldr _⊗_ e []        =  e
    foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

    sum : List ℕ → ℕ
    sum = foldr _+_ 0

    product : List ℕ → ℕ
    product = foldr _*_ 1

    test-prod₀ : product [ 1 , 2 , 3 , 4 ] ≡ 24
    test-prod₀ = refl

    foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) 
                            → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
    foldr-++ _ _ [] ys = refl
    foldr-++ _⊗_ e (x ∷ xs) ys = 
        begin
            foldr _⊗_ e ((x ∷ xs) ++ ys)
            ≡⟨⟩
            foldr _⊗_ e (x ∷ (xs ++ ys))
            ≡⟨⟩
            x ⊗ (foldr _⊗_ e (xs ++ ys))
            ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
            x ⊗ (foldr _⊗_ (foldr _⊗_ e ys) xs)
            ≡⟨⟩
            foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
        ∎
    

    mif-lem : {A B : Set}{f : A → B} → ∀ (xs : List A) → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    mif-lem [] = refl
    mif-lem {f = f}(x ∷ xs) = 
        begin
            map f (x ∷ xs)
            ≡⟨⟩
            f x ∷ map f xs
            ≡⟨ cong ((f x) ∷_) (mif-lem {f = f} xs) ⟩
            f x ∷ (foldr (λ x xs → f x ∷ xs) [] xs)
            ≡⟨⟩
            foldr (λ x xs → f x ∷ xs) [] (x ∷ xs)
        ∎


    map-is-foldr : ∀ {A B : Set} {f : A → B} 
                                → map f ≡ foldr (λ x xs → f x ∷ xs) []
    map-is-foldr = plfa.part1.Isomorphism.extensionality (mif-lem)

    fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
    fold-Tree f g (leaf x) = f x
    fold-Tree f g (node t1 v t2) = g (fold-Tree f g t1) v (fold-Tree f g t2)

    map-is-fold-Tree : ∀ {A B C D : Set} → (f : A → C) → (g : B → D)
                            → map-Tree f g ≡ fold-Tree {A} {B} {Tree C D} (λ x → leaf (f x)) (λ l v r → node l (g v) r)
    map-is-fold-Tree f g = plfa.part1.Isomorphism.extensionality (λ t → misft-lem f g t)
        where
            misft-lem : ∀ {A B C D : Set} → (f : A → C) → (g : B → D) → ∀ (t : Tree A B)
                                → map-Tree f g t ≡ fold-Tree {A} {B} {Tree C D} (λ x → leaf (f x)) (λ l v r → node l (g v) r) t
            misft-lem f g (leaf x) = refl
            misft-lem f g (node t1 v t2) rewrite misft-lem f g t1 | misft-lem f g t2 = refl

    -- Monoids
    record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
        field
            assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
            identityˡ : ∀ (x : A) → e ⊗ x ≡ x
            identityʳ : ∀ (x : A) → x ⊗ e ≡ x

    open IsMonoid

    +-monoid : IsMonoid _+_ 0
    +-monoid =
        record
            { 
                assoc = +-assoc ; 
                identityˡ = +-identityˡ ;
                identityʳ = +-identityʳ
            }

    *-monoid : IsMonoid _*_ 1
    *-monoid =
        record
            { assoc = *-assoc
            ; identityˡ = *-identityˡ
            ; identityʳ = *-identityʳ
            }

    ++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
    ++-monoid =
        record
            { assoc = ++-assoc
            ; identityˡ = ++-identityˡ
            ; identityʳ = ++-identityʳ
            }
    
    foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
                                ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
    foldr-monoid _⊗_ e monoid [] y = sym (identityˡ monoid y)
    foldr-monoid _⊗_ e monoid (x ∷ xs) y = 
        begin
            foldr _⊗_ y (x ∷ xs)
            ≡⟨⟩
            x ⊗ (foldr _⊗_ y xs)
            ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e monoid xs y) ⟩
            x ⊗ (foldr _⊗_ e xs ⊗ y)
            ≡⟨ sym (assoc monoid x (foldr _⊗_ e xs) y) ⟩
            (x ⊗ foldr _⊗_ e xs) ⊗ y
            ≡⟨⟩
            foldr _⊗_ e (x ∷ xs) ⊗ y
        ∎

    foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e 
                            → ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
    foldr-monoid-++ _⊗_ e monoid xs ys = 
        begin
            foldr _⊗_ e (xs ++ ys)
            ≡⟨ foldr-++ _⊗_ e xs ys ⟩
            foldr _⊗_ (foldr _⊗_ e ys) xs
            ≡⟨ foldr-monoid _⊗_ e monoid xs (foldr _⊗_ e ys) ⟩
            foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
        ∎
    
    foldl : {A : Set} → (_⊗_ : A → A → A) → (e : A) → (xs : List A) → A
    foldl _ e [] = e
    foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

    -- Practice foldr-monoid-foldl
    foldl-monoid-lem : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → (xs : List A) → (x : A) 
                                    → foldl _⊗_ (e ⊗ x) xs ≡ foldl _⊗_ x xs
    foldl-monoid-lem _ _ monoid-⊗ xs y rewrite identityˡ monoid-⊗ y = refl

    foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → (xs : List A) → (y : A) 
                                    → y ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ y xs 
    foldl-monoid _⊗_ e monoid-⊗ [] y = 
        begin
            y ⊗ e
            ≡⟨ identityʳ monoid-⊗ y ⟩
            y
        ∎
    foldl-monoid _⊗_ e monoid-⊗ (x ∷ xs) y =
        begin
            y ⊗ foldl _⊗_ e (x ∷ xs)
            ≡⟨⟩
            y ⊗ foldl _⊗_ (e ⊗ x) xs
            ≡⟨ cong (y ⊗_) (foldl-monoid-lem _⊗_ e monoid-⊗ xs x) ⟩
            y ⊗ foldl _⊗_ x xs
            ≡⟨ sym (cong (y ⊗_) (foldl-monoid _⊗_ e monoid-⊗ xs x)) ⟩
            y ⊗ (x ⊗ foldl _⊗_ e xs)
            ≡⟨ sym (assoc monoid-⊗ y x (foldl _⊗_ e xs)) ⟩
            (y ⊗ x) ⊗ foldl _⊗_ e xs
            ≡⟨ foldl-monoid _⊗_ e monoid-⊗ xs (y ⊗ x) ⟩
            foldl _⊗_ (y ⊗ x) xs
            ≡⟨⟩
            foldl _⊗_ y (x ∷ xs)
        ∎

    foldr-monoid-foldl-lem : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → (xs : List A) → (y : A)
                                    → foldl _⊗_ y xs ≡ foldl _⊗_ (e ⊗ y) xs
    foldr-monoid-foldl-lem _⊗_ e monoid-⊗ xs y rewrite identityˡ monoid-⊗ y = refl

    foldr-monoid-foldl-lem₁  : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
                            → IsMonoid _⊗_ e → (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
    foldr-monoid-foldl-lem₁ _ _  monoid-⊗ [] = refl
    foldr-monoid-foldl-lem₁ _⊗_ e monoid-⊗ (x ∷ xs) = 
        begin
            foldr _⊗_ e (x ∷ xs)
            ≡⟨⟩
            x ⊗ (foldr _⊗_ e xs)
            ≡⟨ cong (x ⊗_) (foldr-monoid-foldl-lem₁ _⊗_ e monoid-⊗ xs) ⟩
            x ⊗ foldl _⊗_ e xs
            ≡⟨ foldl-monoid _⊗_ e monoid-⊗ xs x ⟩
            foldl _⊗_ x xs
            ≡⟨ foldr-monoid-foldl-lem _⊗_ e monoid-⊗ xs x ⟩
            foldl _⊗_ (e ⊗ x) xs
            ≡⟨⟩
            foldl _⊗_ e (x ∷ xs)
        ∎
    foldr-monoid-foldl-lem₂   : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
                            → IsMonoid _⊗_ e → (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
    foldr-monoid-foldl-lem₂ _ _  monoid-⊗ [] = refl
    foldr-monoid-foldl-lem₂ _⊗_ e monoid-⊗ (x ∷ xs) rewrite 
                          foldr-monoid-foldl-lem₁ _⊗_ e monoid-⊗ xs
                        | foldl-monoid _⊗_ e monoid-⊗ xs x
                        | identityˡ monoid-⊗ x = refl

    foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
                            → IsMonoid _⊗_ e → (xs : List A) → foldr _⊗_ e ≡ foldl _⊗_ e
    foldr-monoid-foldl f e monoid-⊗ _ = plfa.part1.Isomorphism.extensionality(λ lst → foldr-monoid-foldl-lem₁ f e monoid-⊗ lst)

    -- All
    data All {A : Set} (P : A → Set) : List A → Set where
        []  : All P []
        _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

    -- Any
    data Any {A : Set} (P : A → Set) : List A → Set where
        here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
        there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

    infix 4 _∈_ _∉_

    _∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
    x ∈ xs = Any (x ≡_) xs

    _∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
    x ∉ xs = ¬ (x ∈ xs)

    All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) 
                                    → All P (xs ++ ys) ⇔ (All P xs × All P ys)
    All-++-⇔ xs ys = 
        record
        {
            to = to xs ys ;
            from = from xs ys
        } where
            to : ∀ {A : Set} {P : A → Set} (xs ys : List A) 
                                    → All P (xs ++ ys) → (All P xs × All P ys)
            to [] ys all = ⟨ [] , all ⟩
            to (x ∷ xs) ys (ps ∷ all) with (to xs ys all)
            ... | ⟨ all-xs , all-ys ⟩ = ⟨ ps ∷ all-xs , all-ys ⟩

            from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (All P xs × All P ys) → All P (xs ++ ys)
            from [] ys ⟨ [] , all-ys ⟩ = all-ys
            from (x ∷ xs) ys ⟨ px ∷ all-xs , all-ys ⟩ = px ∷ (from xs ys ⟨ all-xs , all-ys ⟩)

    -- Exercise Any-++-⇔
    Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) ⇔ ((Any P xs) ⊎ (Any P ys))
    Any-++-⇔ xs ys = 
        record
            {
                to = to-lem xs ys ;
                from = from-lem xs ys
            } where
                to-lem : ∀ {A : Set} {P : A → Set} (xs ys : List A) 
                    → Any P (xs ++ ys) →  (Any P xs) ⊎ (Any P ys)
                to-lem [] ys any-ys = inj₂ any-ys
                to-lem (x ∷ xs) _ (here px) = inj₁ (here px)
                to-lem (x ∷ xs) ys (there in-xs++ys) with to-lem xs ys in-xs++ys
                ... | inj₁ in-xs = inj₁ (there in-xs)
                ... | inj₂ in-ys = inj₂ in-ys
                
                from-lem : ∀ {A : Set} {P : A → Set} (xs ys : List A) 
                    → (Any P xs) ⊎ (Any P ys) → Any P (xs ++ ys)
                from-lem _ _ (inj₁ (here px))              = here px
                from-lem [] ys (inj₂ in-ys)                = in-ys
                from-lem (x ∷ xs) ys (inj₁ (there in-xs)) = there (from-lem xs ys (inj₁ in-xs))
                from-lem (x ∷ xs) ys (inj₂ in-ys)         = there (from-lem xs ys (inj₂ in-ys))
    
    -- Exercise All-++-≃
    All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) 
                                    → All P (xs ++ ys) ≃ (All P xs × All P ys)
    All-++-≃ xs ys = 
        record
        {
            to = to xs ys ;
            from = from xs ys ;
            from∘to = from-to-lem xs ys ;
            to∘from = to-from-lem xs ys
        } where
            to : ∀ {A : Set} {P : A → Set} (xs ys : List A) 
                                    → All P (xs ++ ys) → (All P xs × All P ys)
            to [] ys all = ⟨ [] , all ⟩
            to (x ∷ xs) ys (ps ∷ all) with (to xs ys all)
            ... | ⟨ all-xs , all-ys ⟩ = ⟨ ps ∷ all-xs , all-ys ⟩

            from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (All P xs × All P ys) → All P (xs ++ ys)
            from [] ys ⟨ [] , all-ys ⟩ = all-ys
            from (x ∷ xs) ys ⟨ px ∷ all-xs , all-ys ⟩ = px ∷ (from xs ys ⟨ all-xs , all-ys ⟩)
            from-to-lem : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (ev : All P (xs ++ ys)) 
                            → from xs ys (to xs ys ev) ≡ ev
            from-to-lem [] ys in-ys = refl
            from-to-lem (x ∷ xs) ys (px ∷ all) rewrite from-to-lem xs ys all = refl

            to-from-lem : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (ev : All P xs × All P ys) 
                            → to xs ys (from xs ys ev) ≡ ev
            to-from-lem [] ys ⟨ [] , all-ys ⟩ = refl
            to-from-lem (x ∷ xs) ys ⟨ px ∷ all-xs , all-ys ⟩ rewrite to-from-lem xs ys ⟨ all-xs , all-ys ⟩ = refl