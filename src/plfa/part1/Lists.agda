module plfa.part1.Lists where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; sym; trans; cong)
    open Eq.≡-Reasoning
    open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
    open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
    open import Relation.Nullary using (¬_; Dec; yes; no)
    open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
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
        