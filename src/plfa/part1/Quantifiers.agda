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

    eta-to : {A : Set}{B C : A → Set}{x : A}{f : A → B x × C x} → f ≡ (λ x → ⟨ (proj₁ ∘ f) x , (proj₂ ∘ f) x ⟩)
    eta-to = refl

    eta-times : {A B : Set}{w : A × B} → w ≡ ⟨ proj₁ w , proj₂ w ⟩
    eta-times = refl

    data Σ (A : Set) (B : A → Set) : Set where
         ⟨_,_⟩ : (x : A) → B x → Σ A B

    Σ-syntax = Σ
    infix 2 Σ-syntax
    syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

    ∃ : ∀ {A : Set} (B : A → Set) → Set
    ∃ {A} B = Σ A B

    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B

    ∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
            → (∀ x → B x → C) → ∃[ x ] B x → C
    ∃-elim  f ⟨ x , y ⟩ = f x y

    open _≃_

    ∀∃-curring : ∀ {A : Set} {B : A → Set} {C : Set}
                → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
    ∀∃-curring =
        record
        {
            to = λ{f → λ{⟨ x , y ⟩ → f x y}} ;
            from = λ {g → λ{x → λ{bx → g ⟨ x , bx ⟩}}} ;
            from∘to = λ{f → refl} ;
            to∘from = λ{g → extensionality (λ{⟨ x , y ⟩ → refl})}
        }

    -- to ∀∃-curring = λ{f → λ{⟨ x , y ⟩ → f x y}}
    -- from ∀∃-curring = λ {g → λ{x → λ{bx → g ⟨ x , bx ⟩}}}
    -- from∘to ∀∃-curring = λ{f → refl}
    -- to∘from ∀∃-curring = λ{f → extensionality (λ{⟨ x , y ⟩ → refl})}

    -- Exercise
    ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
                → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
    ∃-distrib-⊎ =
        record
            {
                to = λ{⟨ x , (inj₁ bx) ⟩ → inj₁ (⟨ x , bx ⟩) ; ⟨ x , (inj₂ cx) ⟩ → inj₂ (⟨ x ,  cx ⟩)} ;
                from = λ{(inj₁ (⟨ x , bx ⟩)) → ⟨ x , (inj₁ bx) ⟩ ; (inj₂ (⟨ x , cx ⟩)) → ⟨ x , (inj₂ cx) ⟩} ;
                from∘to = λ {⟨ x , (inj₁ bx) ⟩ → refl ; ⟨ x , (inj₂ cx) ⟩ → refl} ;
                to∘from = λ {(inj₁ (⟨ x , bx ⟩)) → refl ; (inj₂ (⟨ x , cx ⟩)) → refl}
            }

    -- ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
    --               → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
    -- ∃×-implies-×∃ =
    --     record
    --         {
    --             to = λ{⟨ x , < bx , cx > ⟩ → < ⟨ x , bx ⟩ , ⟨ x , cx ⟩ >} ;
    --             from = λ{< ⟨ x , bx ⟩ , ⟨ x , cx ⟩ > → ⟨ x , < bx , cx > ⟩} ;
    --             from∘to = λ {_ → refl} ;
    --             to∘from = λ {_ → refl}
    --         }

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

    even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (m * 2 ≡ n)
    odd-∃  : ∀ {n : ℕ} → odd n →  ∃[ m ] (1 + m * 2 ≡ n)

    even-∃ (even-zero) = ⟨ zero , refl ⟩
    even-∃ (even-suc oddn) with odd-∃ oddn
    ...                   | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

    odd-∃ (odd-suc evn) with even-∃ evn
    ...                   |  ⟨ m , refl ⟩ = ⟨ m , refl ⟩

    ∃-even : ∀ {n : ℕ} → ∃[ m ] (m * 2 ≡ n) → even n
    ∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → odd n

    ∃-even ⟨ zero , refl ⟩ = even-zero
    -- 2 + (m * 2) | 1 + (m * 2)
    ∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)

    ∃-odd ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

    -- Practice
    -- ∃-even-p : ∀ {n : ℕ} → ∃[ m ] (2 * m ≡ n) → even n
    -- ∃-odd-p  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n

    -- -- 2 * suc m = suc m + 1 * (suc m) = suc (m + suc (m + zero)) === n
    -- ∃-even-lem : ∀ { n : ℕ} → (n + (n + zero) + 1) ≡ n + suc (n + zero)


    -- ∃-even-p ⟨ zero , refl ⟩ = even-zero
    -- ∃-even-p ⟨ suc m , refl ⟩ = even-suc (∃-odd-p ⟨ m , refl ⟩)
    -- -- m + 1 * m + 1 === n
    -- ∃-odd-p ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)
