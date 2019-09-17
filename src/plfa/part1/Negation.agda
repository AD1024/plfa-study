module plfa.part1.Negation where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import Data.Nat using (ℕ; zero; suc)
    open import Data.Empty using (⊥; ⊥-elim)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import plfa.part1.Connectives using (_×_; ⟨_,_⟩)
    open import Function using (_∘_)
    open import plfa.part1.Isomorphism using (_≃_; extensionality)
    open import Relation.Binary.PropositionalEquality using (cong)
    open import plfa.part1.Naturals_Relations using (_<_; s<s; z<s)

    ¬_ : Set → Set
    ¬ A = A → ⊥


    ¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
    ¬-elim ¬x x = ¬x x

    infix 3 ¬_

    ¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
    ¬¬-intro x ¬x = ¬x x

    -- not not not A = A -> false -> false -> false
    ¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
    ¬¬¬-elim ¬¬¬x = λ x -> ¬¬¬x (¬¬-intro x)

    contraposition : ∀ {A B : Set}
                    → (A → B)
                        -----------
                    → (¬ B → ¬ A)
    contraposition f ¬B A = ¬B (f A)

    _≢_ : ∀ {A : Set} → A → A → Set
    x ≢ y  =  ¬ (x ≡ y)
    
    peano : ∀ {m : ℕ} → zero ≢ suc m
    peano = λ()

    assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
    assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

    <-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
    <-irreflexive {n = zero} ()
    <-irreflexive {n = suc n'} (s<s n<n) = <-irreflexive n<n

    data Trichotomy : ℕ → ℕ → Set where
        le  :  {m n : ℕ} → m < n → Trichotomy m n
        eq  :  {m n : ℕ} → m ≡ n → Trichotomy m n
        ge  :  {m n : ℕ} → n < m → Trichotomy m n

    trichotomy : (m n : ℕ) → Trichotomy m n
    trichotomy zero (suc n) = le z<s
    trichotomy zero zero = eq refl
    trichotomy (suc m) zero = ge z<s
    trichotomy (suc m) (suc n) with trichotomy m n
    ...                         | eq refl = eq refl
    ...                         | le m<n  = le (s<s m<n)
    ...                         | ge n<m  = ge (s<s n<m)

    -- A U B -> _|_
    ⊎-dual-× : {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
    ⊎-dual-× = 
        record
             {
                 to = λ {f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩} ;
                 from = λ {⟨ f , g ⟩ → λ {(inj₁ x) → f x; (inj₂ y) → g y}} ;
                 from∘to = λ{f → extensionality(λ{(inj₁ x) → refl; (inj₂ y) → refl})} ;
                 to∘from = λ{⟨ f , g ⟩ → refl}
             }
    