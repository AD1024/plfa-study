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