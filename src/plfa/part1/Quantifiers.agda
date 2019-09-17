module plfa.part1.Quantifiers where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
    open import Relation.Nullary using (¬_)
    open import Data.Product using (_×_; proj₁; proj₂ ) renaming (_,_ to ⟨_,_⟩)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Function using (_∘_)
    open import plfa.part1.Isomorphism using (_≃_; extensionality)
    
    η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
    η-× ⟨ x , y ⟩ = refl

    ∀-elim : {A : Set}{B : A → Set} → (L : ∀ (x : A) → B x) → (M : A) → B M
    ∀-elim L M = L M

    -- Exercise
    ∀-distrib-× : ∀ {A : Set}{B C : A → Set} →
                    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
    ∀-distrib-× =
        record
        {
            to = λ{f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩} ;
            from = λ{⟨ A→Bx , A→Cx ⟩ → λ{x → ⟨ A→Bx x , A→Cx x ⟩}} ;
            from∘to = λ{f → refl} ;
            to∘from = λ{prod → η-× prod}
        }

    -- Practice
    ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
    ⊎∀-implies-∀⊎ (inj₁ A→Bx) = λ x → inj₁ (A→Bx x)
    ⊎∀-implies-∀⊎ (inj₂ A→Cx) = λ x → inj₂ (A→Cx x)

    