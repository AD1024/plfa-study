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