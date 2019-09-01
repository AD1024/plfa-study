module plfa.Equality where
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
            ≡⟨ +-identity m ⟩
            m
            ≡⟨⟩
            zero + m
        ∎ 
    +-comm m (suc n) = 
        begin
            m + (suc n)
            ≡⟨ +-suc m n ⟩
            suc (m + n)
            ≡⟨ cong suc (+-comm m n) ⟩
            suc (n + m)
        ∎

    data _≤_ : ℕ -> ℕ -> Set where
        z≤n : ∀ {n : ℕ} -> zero ≤ n
        s≤s : ∀ {m n : ℕ} -> m ≤ n -> suc m ≤ suc n
    
    infix 4 _≤_

    trans' : {m n p : ℕ} -> m ≤ n -> n ≤ p -> m ≤ p
    trans' z≤n _ = z≤n
    trans' (s≤s m≤n) (s≤s n≤p) = (s≤s (trans' m≤n n≤p))

    ≤-refl : ∀ {n : ℕ} -> n ≤ n
    ≤-refl {zero} = z≤n
    ≤-refl {suc n} = (s≤s ≤-refl) 

    module ≤-Reasoning where
        infix  1 Proof_
        infixr 2 _≤⟨⟩_ _≤⟨_⟩_
        infix  3 _QED

        Proof_ : ∀ {x y : ℕ}
            → x ≤ y
            -----
            → x ≤ y
        Proof x≤y  =  x≤y

        _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
            → x ≤ y
            -----
            → x ≤ y
        x ≤⟨⟩ x≤y  =  x≤y

        _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
            → x ≤ y
            → y ≤ z
            -----
            → x ≤ z
        x ≤⟨ x≤y ⟩ y≤z  =  trans' x≤y y≤z

        _QED  : ∀ (x : ℕ)
            -----
            → x ≤ x
        x QED  =  ≤-refl

    open ≤-Reasoning
    
    +-mono-≤ : ∀ (n p q : ℕ) -> p ≤ q -> n + p ≤ n + q
    +-mono-≤ zero p q p≤q = 
        Proof
            p
            ≤⟨ p≤q ⟩
            q
        QED
    
    +-mono-≤ (suc n) p q p≤q = 
        Proof
            suc (n + p)
            ≤⟨ s≤s (+-mono-≤ n p q p≤q) ⟩
            suc (n + q)
        QED

    -- postulate +-comm : ∀ {m n : ℕ} -> m + n ≡ n + m

    ≡-in-≤ : ∀ {m n : ℕ} -> m ≡ n -> m ≤ n
    ≡-in-≤ {m = zero} _ = z≤n
    ≡-in-≤ {m = suc x} refl = s≤s (≤-refl {x})  

    +-mono-l-≤ : ∀ (m n p : ℕ)
        -> m ≤ n -> m + p ≤ n + p
    +-mono-l-≤ m n p m≤n = 
        Proof
            m + p
            ≤⟨ ≡-in-≤ (+-comm m p) ⟩ 
            p + m
            ≤⟨ +-mono-≤ p m n m≤n ⟩
            p + n
            ≤⟨ ≡-in-≤ (+-comm p n) ⟩
            n + p
        QED

    +-mono-≤-tot : ∀ (m n p q : ℕ)
        -> m ≤ n
        -> p ≤ q
        -> m + p ≤ n + q
    +-mono-≤-tot m n p q m≤n p≤q =
        Proof
            m + p
            ≤⟨ +-mono-l-≤ m n p m≤n ⟩
            n + p
            ≤⟨ +-mono-≤ n p q p≤q ⟩
            n + q
        QED 

    -- Rewriting
    data even : ℕ → Set
    data odd  : ℕ → Set

    data even where
        even-zero : even zero
        even-suc : ∀ {n : ℕ}
            → odd n
            ------------
            → even (suc n)

    data odd where
        odd-suc : ∀ {n : ℕ}
            → even n
            -----------
            → odd (suc n)

    {-# BUILTIN EQUALITY _≡_ #-}

    even-comm : ∀ (m n : ℕ) -> even (m + n) -> even (n + m)
    even-comm m n ev rewrite +-comm m n = ev

    _≐_ : ∀ {A : Set} (x y : A) -> Set₁
    _≐_ {A} x y = ∀ (P : A -> Set) -> P x -> P y

    refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
    refl-≐ P  px = px
    --     P (P x) : corresponds to ∀ (P) -> P x -> P y




