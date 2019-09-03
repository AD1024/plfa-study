module plfa.Connectives where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open Eq.≡-Reasoning
    open import Data.Nat using (ℕ)
    open import Function using (_∘_)
    open import plfa.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
    open plfa.Isomorphism.≃-Reasoning
    open _⇔_

    data _×_ (A B : Set) : Set where
        ⟨_,_⟩ :
            A → B
            -----
            → A × B
    
    proj₁ : ∀ {A B : Set} -> A × B -> A
    proj₁ ⟨ x , y ⟩ = x

    proj₂ : ∀ {A B : Set} -> A × B -> B
    proj₂ ⟨ x , y ⟩ = y

    η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
    η-× ⟨ x , y ⟩ = refl

    infixr 2 _×_

    ×-comm : ∀ {A B : Set} -> A × B ≃ B × A
    ×-comm = 
        record 
        {
            to = λ{⟨ x , y ⟩ -> ⟨ y , x ⟩} ;
            from = λ{⟨ y , x ⟩ -> ⟨ x , y ⟩} ;
            from∘to = λ{⟨ x , y ⟩ -> refl} ;
            to∘from = λ{⟨ y , x ⟩ -> refl}
        }

    ×-assoc : ∀ {A B C : Set} -> (A × B) × C ≃ A × (B × C)
    ×-assoc = 
        record
            {
                to = λ{⟨ ⟨ x , y ⟩ , z ⟩ -> ⟨ x , ⟨ y , z ⟩ ⟩} ;
                from = λ{⟨ x , ⟨ y , z ⟩ ⟩ -> ⟨ ⟨ x , y ⟩ , z ⟩} ;
                from∘to = λ{⟨ ⟨ x , y ⟩ , z ⟩ -> refl} ;
                to∘from = λ{⟨ x , ⟨ y , z ⟩ ⟩ -> refl}
            }
    
    ⇔≃× : ∀ {A B : Set} -> A ⇔ B ≃ (A -> B) × (B -> A)
    ⇔≃× =
        record
            {
                to = λ{A⇔B -> ⟨ to A⇔B , from A⇔B ⟩} ;
                from = λ{
                    prod -> record
                                {
                                    to = proj₁ prod ;
                                    from = proj₂ prod
                                }
                } ;
                from∘to = λ{x -> refl} ;
                to∘from = λ{y ->  η-× y}
            }

    data ⊤ : Set where
        tt :
            --
            ⊤
    
    η-⊤ : ∀ (w : ⊤) → tt ≡ w
    η-⊤ tt = refl

    data _⊎_ (A B : Set) : Set where
        inj₁ :
            A
            -----
            → A ⊎ B

        inj₂ :
            B
            -----
            → A ⊎ B

    case-⊎ : ∀ {A B C : Set} -> (A -> C) -> (B -> C) -> A ⊎ B -> C
    case-⊎ f g (inj₁ x) = f x
    case-⊎ f g (inj₂ y) = g y

    η-⊎ : ∀ {A B : Set} -> (w : A ⊎ B) -> case-⊎ inj₁ inj₂ w ≡ w
    η-⊎ (inj₁ x) = refl
    η-⊎ (inj₂ y) = refl

    infix 1 _⊎_

    ⊎-comm : ∀ {A B : Set} -> A ⊎ B ≃ B ⊎ A
    ⊎-comm = 
        record
            {
                to = λ{(inj₁ x) -> inj₂ x ; (inj₂ y) -> inj₁ y} ;
                from = λ{(inj₁ x) -> inj₂ x ; (inj₂ y) -> inj₁ y} ;
                from∘to = λ{
                    (inj₁ x) -> refl ;
                    (inj₂ y) -> refl
                } ;
                to∘from = λ{
                    (inj₁ x) -> refl ;
                    (inj₂ y) -> refl 
                }
            }
    ⊎-assoc : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
    ⊎-assoc = 
        record
            {
                to = λ{
                    (inj₁ (inj₁ x)) -> inj₁ x ;
                    (inj₁ (inj₂ y)) -> inj₂ (inj₁ y) ;
                    (inj₂ z)        -> inj₂ (inj₂ z)
                } ;
                from = λ{
                    (inj₁ x) -> inj₁ (inj₁ x) ;
                    (inj₂ (inj₁ y)) -> inj₁ (inj₂ y) ;
                    (inj₂ (inj₂ z)) -> inj₂ z
                } ;
                from∘to = λ{
                    (inj₁ (inj₁ x)) -> refl ; 
                    (inj₁ (inj₂ y)) -> refl ; 
                    (inj₂ z) -> refl
                } ;
                to∘from = λ{
                    (inj₁ x) -> refl ;
                    (inj₂ (inj₁ y)) -> refl ;
                    (inj₂ (inj₂ z)) -> refl
                }
            }

    data ⊥ : Set where
        -- no clauses!

    ⊥-identity-l : ∀ {A : Set} -> ⊥ ⊎ A ≃ A
    ⊥-identity-l = 
        record {
            to = λ{(inj₂ x) -> x} ;
            from = λ{x -> inj₂ x} ;
            from∘to = λ{(inj₂ x) -> refl} ;
            to∘from = λ{x -> refl}
        }
    -- Similar proof of ⊥-identity-r ... skipped