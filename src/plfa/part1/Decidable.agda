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
    open import plfa.part1.Relations using (_<_; z<s; s<s)
    open import plfa.part1.Isomorphism using (_⇔_)

    infix 4 _≤_

    data _≤_ : ℕ → ℕ → Set where
        z≤n : ∀ {n : ℕ}
            --------
            → zero ≤ n

        s≤s : ∀ {m n : ℕ}
            → m ≤ n
            -------------
            → suc m ≤ suc n

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

    data Dec (A : Set) : Set where
        yes :   A → Dec A
        no  : ¬ A → Dec A

    ¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
    ¬s≤z ()

    ¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
    ¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

    _≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    zero ≤? n = yes z≤n
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
