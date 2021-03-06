module Equality where
    data _≡_ {A : Set} (x : A) : A -> Set where
        refl : x ≡ x

    infix 4 _≡_

    sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
    sym refl = refl

    trans : ∀ {A : Set}{x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
    trans refl refl = refl

    cong : ∀ {A B : Set}{x y : A}(f : A → B) -> x ≡ y -> f x ≡ f y
    cong f refl = refl

    cong₂ : ∀ {A B C : Set}(f : A → B → C) {u x : A}{v y : B} -> u ≡ x -> v ≡ y -> f u v ≡ f x y
    cong₂ f refl refl = refl  

    cong-app : ∀ {A B : Set}{f g : A → B} -> f ≡ g -> ∀ {x : A} -> f x ≡ g x
    cong-app refl = refl

    subst : ∀ {A : Set}{x y : A} (P : A → Set) -> x ≡ y -> P x -> P y
    subst P refl px = px

    -- Code from PLFA (https://plfa.github.io/Equality/#5128)
    module ≡-Reasoning {A : Set} where

        infix  1 begin_
        infixr 2 _≡⟨⟩_ _≡⟨_⟩_
        infix  3 _∎

        begin_ : ∀ {x y : A}
            → x ≡ y
            -----
            → x ≡ y
        begin x≡y  =  x≡y

        _≡⟨⟩_ : ∀ (x : A) {y : A}
            → x ≡ y
            -----
            → x ≡ y
        x ≡⟨⟩ x≡y  =  x≡y

        _≡⟨_⟩_ : ∀ (x : A) {y z : A}
            → x ≡ y
            → y ≡ z
            -----
            → x ≡ z
        x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

        _∎ : ∀ (x : A)
            -----
            → x ≡ x
        x ∎  =  refl

    open ≡-Reasoning
    
    trans₀ : ∀ {A : Set}{x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
    trans₀ {A} {x} {y} {z} x==y y==z = 
        begin
            x
            ≡⟨ x==y ⟩
            -- Since y ≡⟨ y==z ⟩ z simply yields y==z, we can replace this term with y==z
            y
            ≡⟨ y==z ⟩
            z
        ∎

    -- Code from PLFA
    data ℕ : Set where
        zero : ℕ
        suc  : ℕ → ℕ
    
    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    (suc m) + n = suc (m + n)

    postulate
        +-identity : ∀ (m : ℕ) → m + zero ≡ m
        +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
    
    +-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
    +-comm m zero = 
        begin
            m + zero
            ≡⟨ +-identity ⟩
            m
            ≡⟨⟩
            zero + m
        ∎ 
    +-comm m (suc n) = 
        