module plfa.part1.Decidable where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open Eq.≡-Reasoning
    open import Data.Nat using (ℕ; zero; suc)
    open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Relation.Nullary using (¬_)
    open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
    open import Data.Unit using (⊤; tt)
    open import Data.Empty using (⊥; ⊥-elim)
    open import plfa.part1.Relations using (_<_; z<s; s<s; _≤_; z≤s; s≤s)
    open import plfa.part1.Isomorphism using (_⇔_)

    data Bool : Set where
        true  : Bool
        false : Bool

    infix 4 _≤ᵇ_

    _≤ᵇ_ : ℕ → ℕ → Bool
    zero ≤ᵇ n = true
    suc m ≤ᵇ zero = false
    suc m ≤ᵇ suc n = m ≤ᵇ n

    _ : (2 ≤ᵇ 4) ≡ true
    _ = begin
            2 ≤ᵇ 4
            ≡⟨⟩
            1 ≤ᵇ 3
            ≡⟨⟩
            0 ≤ᵇ 2
            ≡⟨⟩
            true
        ∎
    
    T : Bool → Set
    T true  = ⊤
    T false = ⊥

    T→≡ : ∀ (b : Bool) → T b → b ≡ true
    T→≡ true tt = refl
    T→≡ false ()

    ≡→T : ∀ {b : Bool} → b ≡ true → T b
    ≡→T refl  =  tt

    ≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
    ≤ᵇ→≤ zero n tt = z≤s
    ≤ᵇ→≤ (suc m) zero ()
    ≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)

    ≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
    ≤→≤ᵇ z≤s = tt
    ≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

    data Dec (A : Set) : Set where
        yes :   A → Dec A
        no  : ¬ A → Dec A

    ¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
    ¬s≤z ()

    ¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
    ¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

    _≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    zero ≤? n = yes z≤s
    suc m ≤? zero = no ¬s≤z
    suc m ≤? suc n with m ≤? n
    ... | yes m≤n = yes(s≤s m≤n)
    ... | no ¬m≤n = no (¬s≤s ¬m≤n)

    ¬s<z : ∀ {m : ℕ} → ¬ (m < zero)
    ¬s<z ()

    ¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
    ¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

    _<?_ : ∀ (m n : ℕ) → Dec (m < n)
    zero <? suc n = yes z<s
    m    <? zero  = no ¬s<z
    suc m <? suc n with m <? n
    ... | yes m<n = yes (s<s m<n)
    ... | no ¬m<n = no (¬s<s ¬m<n)

    -- Practice _≡ℕ?_
    s=s-implies-m=n : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    s=s-implies-m=n refl = refl

    z≢s : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
    z≢s ()

    s≢z : ∀ {n : ℕ} → ¬ (suc n ≡ zero)
    s≢z ()

    s≢s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
    s≢s ¬m=n (sm=sn) = ¬m=n (s=s-implies-m=n sm=sn)

    _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
    zero ≡ℕ? zero = yes refl
    zero ≡ℕ? suc n = no z≢s
    suc m ≡ℕ? zero = no s≢z
    suc m ≡ℕ? suc n with m ≡ℕ? n
    ... | yes refl = yes refl
    ... | no m≢n  = no (s≢s m≢n)

    -- _≤?'_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    -- m ≤?' n with m ≤ᵇ n
    -- ... | true = yes (≤ᵇ→≤ m n tt)
    -- ... | false = no (≤→≤ᵇ {m} {n})

    ⌊_⌋ : ∀ {A : Set} → Dec A → Bool
    ⌊ yes x ⌋ = true
    ⌊ no ¬x ⌋ = false

    _≤ᵇ′_ : ℕ → ℕ → Bool
    m ≤ᵇ′ n = ⌊ m ≤? n ⌋

    toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
    toWitness {A} {yes x} tt = x
    toWitness {A} {no ¬x} ()

    fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
    fromWitness {A} {yes x} _ = tt
    fromWitness {A} {no ¬x} x = ¬x x

    ≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
    ≤ᵇ′→≤  =  toWitness

    ≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
    ≤→≤ᵇ′  =  fromWitness

    -- Logical Connectives

    infixr 6 _∧_
    _∧_ : Bool → Bool → Bool
    true  ∧ true  = true
    false ∧ _     = false
    _     ∧ false = false

    infixr 6 _×-dec_
    _×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
    yes x ×-dec yes y = yes ⟨ x , y ⟩
    no ¬x ×-dec _     = no λ{⟨ x , y ⟩ → ¬x x}
    _     ×-dec no ¬y = no λ{⟨ x , y ⟩ → ¬y y}

    infixr 6 _∨_
    _∨_ : Bool → Bool → Bool
    true  ∨ _     = true
    _     ∨ true  = true
    false ∨ false = false

    infixr 5 _⊎-dec_
    _⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec(A ⊎ B)
    yes x ⊎-dec _     = yes (inj₁ x)
    _     ⊎-dec yes y = yes (inj₂ y)
    no ¬x ⊎-dec no ¬y = no λ{(inj₁ x) → ¬x x ; (inj₂ y) → ¬y y}

    not : Bool → Bool
    not true = false
    not false = true

    ¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
    ¬? (yes x) = no (¬¬-intro x)
    ¬? (no ¬x) = yes (¬x)

    _⊃_ : Bool → Bool → Bool
    _     ⊃ true   =  true
    false ⊃ _      =  true
    true  ⊃ false  =  false
    _→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
    _ →-dec (yes y) = yes λ{x → y}
    no ¬x →-dec _   = yes λ{x → ⊥-elim (¬x x)}
    yes x →-dec no ¬y = no λ{x->y → ¬y (x->y x)}

    ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
    ∧-× (yes x) (yes y) = refl
    ∧-× (no ¬x) _       = refl
    ∧-× (yes x) (no ¬y) = refl

    ∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
    ∨-⊎ (yes x) _       = refl
    ∨-⊎ (no ¬x) (yes y) = refl
    ∨-⊎ (no ¬x) (no ¬y) = refl

    not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
    not-¬ (yes x) = refl
    not-¬ (no ¬x) = refl

    -- Exercise
    _iff_ : Bool → Bool → Bool
    true  iff true  = true
    false iff false = true
    true  iff false = false
    false iff true  = false

    _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
    (yes x) ⇔-dec (yes y) = yes (record { to = λ{x → y} ; from = λ {y → x} })
    (no ¬x) ⇔-dec (no ¬y) = yes (record { to = λ{x → ⊥-elim (¬x x)} ; from = λ{y → ⊥-elim (¬y y)}})
    (no ¬x) ⇔-dec (yes y) = no λ{A⇔B → ⊥-elim (¬x (plfa.part1.Isomorphism._⇔_.from A⇔B y))}
    (yes x) ⇔-dec (no ¬y) = no λ{A⇔B → ⊥-elim (¬y (plfa.part1.Isomorphism._⇔_.to   A⇔B x))}

    iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
    iff-⇔ (yes x) (yes y) = refl
    iff-⇔ (no ¬x) (no ¬y) = refl
    iff-⇔ (yes x) (no ¬y) = refl
    iff-⇔ (no ¬x) (yes y) = refl