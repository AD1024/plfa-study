module plfa.part1.Isomorphism where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; cong-app)
    open Eq.≡-Reasoning
    open import Data.Nat using (ℕ; zero; suc; _+_)
    open import Data.Nat.Properties using (+-comm)
    open import Function using (_∘_)

    -- _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
    -- (f ∘ g) = λ {x -> f (g x)}

    postulate
        extensionality : ∀ {A B : Set} {f g : A → B} 
                -> (∀ (x : A) -> f x ≡ g x)
                -> f ≡ g
    
    _+'_ : ℕ -> ℕ -> ℕ
    m +' zero = m
    m +' suc n = suc (m +' n)

    same-app : ∀ (m n : ℕ) -> m +' n ≡ m + n
    same-app m n rewrite +-comm m n = helper m n
        where
        helper : ∀ (m n : ℕ) -> m +' n ≡ n + m
        helper m zero = refl
        helper m (suc n) = cong suc (helper m n)

    same : _+'_ ≡ _+_
    same = extensionality (λ m -> extensionality (λ n -> same-app m n))

    plusZero : ℕ -> ℕ
    plusZero n = n + 0

    id : ℕ -> ℕ
    id x = x

    same-app₀ : ∀ (x : ℕ) -> id x ≡ plusZero x
    same-app₀ x rewrite +-comm x 0 = refl

    same₀ : id ≡ plusZero
    same₀ = extensionality (λ x -> same-app₀ x) 

    infix 0 _≃_
    record _≃_ (A B : Set) : Set where
      field
        to   : A -> B
        from : B -> A
        from∘to : ∀ (x : A) -> from (to x) ≡ x
        to∘from : ∀ (y : B) -> to (from y) ≡ y

    open _≃_ public

    ≃-refl : ∀ {A : Set} -> A ≃ A
    ≃-refl = record
              { to   = λ{x -> x};
                from = λ{y -> y};
                from∘to = λ{x -> refl};
                to∘from = λ{y -> refl}
              }
    ≃-sym : ∀ {A B : Set} -> A ≃ B -> B ≃ A
    ≃-sym A≃B = 
        record 
            {
                to = from A≃B;
                from = to A≃B;
                from∘to = to∘from A≃B;
                to∘from = from∘to A≃B
            }

    ≃-trans : ∀ {A B C : Set} -> A ≃ B -> B ≃ C -> A ≃ C
    ≃-trans A~=B B~=C = 
            record
            {
                to =  to B~=C ∘ to A~=B ;
                from = from A~=B ∘ from B~=C ;
                from∘to = λ{x ->
                    begin
                        (from A~=B ∘ from B~=C) ((to B~=C ∘ to A~=B) x)
                        ≡⟨⟩
                        from A~=B (from B~=C (to B~=C (to A~=B x)))
                        ≡⟨ cong (from A~=B) (from∘to B~=C (to A~=B x)) ⟩
                        from A~=B (to A~=B x)
                        ≡⟨ from∘to A~=B x ⟩
                        x
                    ∎} ;
                to∘from = λ{y ->
                    begin
                        (to B~=C ∘ to A~=B) ((from A~=B ∘ from B~=C) y)
                        ≡⟨⟩
                        to B~=C (to A~=B (from A~=B (from B~=C y)))
                        ≡⟨ cong (to B~=C) (to∘from A~=B (from B~=C y)) ⟩
                        to B~=C (from B~=C y)
                        ≡⟨ to∘from B~=C y ⟩
                        y
                    ∎
                }
            }

    module ≃-Reasoning where

        infix  1 ≃-begin_
        infixr 2 _≃⟨_⟩_
        infix  3 _≃-∎

        ≃-begin_ : ∀ {A B : Set}
            → A ≃ B
            -----
            → A ≃ B
        ≃-begin A≃B = A≃B

        _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
            → A ≃ B
            → B ≃ C
            -----
            → A ≃ C
        A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

        _≃-∎ : ∀ (A : Set)
            -----
            → A ≃ A
        A ≃-∎ = ≃-refl

    open ≃-Reasoning public

    infix 0 _≲_
    record _≲_ (A B : Set) : Set where
        field
            to      : A → B
            from    : B → A
            from∘to : ∀ (x : A) → from (to x) ≡ x
    open _≲_ public

    ≲-refl : ∀ {A : Set} -> A ≲ A
    ≲-refl = 
        record
            {
                to = λ{x -> x} ;
                from = λ{y -> y} ;
                from∘to = λ{y -> refl}
            }
    
    ≲-trans : ∀ {A B C : Set} -> A ≲ B -> B ≲ C -> A ≲ C
    ≲-trans A≲B B≲C = 
        record
            {
                to = (to B≲C) ∘ (to A≲B) ;
                from = (from A≲B) ∘ (from B≲C) ;
                from∘to = λ{y -> 
                    begin
                        (from A≲B ∘ from B≲C) ((to B≲C ∘ to A≲B) y)
                        ≡⟨⟩
                        from A≲B (from B≲C (to B≲C (to A≲B y)))
                        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B y)) ⟩
                        from A≲B (to A≲B y)
                        ≡⟨ from∘to A≲B y ⟩
                        y
                    ∎        
                }
            }
    
    ≲-antisym : ∀ {A B : Set} 
            -> (A≲B : A ≲ B)
            -> (B≲A : B ≲ A) 
            -> (to A≲B ≡ from B≲A)
            -> (from A≲B ≡ to B≲A)
            -> A ≃ B
    ≲-antisym A≲B B≲A t≡f f≡t = 
            record
                {
                    to = to A≲B ;
                    from = from A≲B ;
                    from∘to = from∘to A≲B ;
                    to∘from = λ{y ->
                        begin
                            to A≲B (from A≲B y)
                            ≡⟨ cong (to A≲B) (cong-app f≡t y) ⟩
                            to A≲B (to B≲A y)
                            ≡⟨ cong-app t≡f (to B≲A y) ⟩
                            from B≲A (to B≲A y)
                            ≡⟨ from∘to B≲A y ⟩
                            y
                        ∎
                    }
                }

    module ≲-Reasoning where
        infix  1 ≲-begin_
        infixr 2 _≲⟨_⟩_
        infix  3 _≲-∎

        ≲-begin_ : ∀ {A B : Set}
            → A ≲ B
            -----
            → A ≲ B
        ≲-begin A≲B = A≲B

        _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
            → A ≲ B
            → B ≲ C
            -----
            → A ≲ C
        A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

        _≲-∎ : ∀ (A : Set)
            -----
            → A ≲ A
        A ≲-∎ = ≲-refl

    open ≲-Reasoning

    -- Exercise
    ≃-implies-≲ : ∀ {A B : Set} -> A ≃ B -> A ≲ B
    ≃-implies-≲ A≃B = 
        record
            {
                to = to A≃B ;
                from = from A≃B ;
                from∘to = from∘to A≃B
            }
    
    record _⇔_ (A B : Set) : Set where
        field
            to    : A → B
            from  : B → A
    open _⇔_ public

    ⇔-refl : ∀ {A : Set} -> A ⇔ A
    ⇔-refl = 
        record
            {
                to = λ{x -> x} ;
                from = λ{y -> y}
            }
    
    ⇔-sym : ∀ {A B : Set} -> A ⇔ B -> B ⇔ A
    ⇔-sym A⇔B = 
        record
            {
                to  = from A⇔B;
                from = to A⇔B
            }
    
    ⇔-trans : ∀ {A B C : Set} -> A ⇔ B -> B ⇔ C -> A ⇔ C
    ⇔-trans A⇔B B⇔C = 
        record
            {
                to = to B⇔C ∘ to A⇔B ;
                from = from A⇔B ∘ from B⇔C
            }