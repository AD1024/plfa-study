module Learn where
  open import Agda.Builtin.Equality
  open import Agda.Builtin.List
  open import Agda.Builtin.Bool

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong)
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Nat.Properties using (+-comm)

-- Chapter 3: Relations

  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} → zero ≤ n
    s≤s : ∀ {n m : ℕ} → m ≤ n -> suc m ≤ suc n

  infix 4 _≤_

  twoLeqFour : 2 ≤ 4
  twoLeqFour = s≤s (s≤s (z≤n))

  inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
  inv-s≤s (s≤s m<=n) = m<=n 

  inv-z<=n : ∀ {m : ℕ} → m ≤ zero →  m ≡ zero
  inv-z<=n z≤n = refl

  ≤-trans : ∀ {m n p : ℕ}
            → m ≤ n → n ≤ p → m ≤ p
  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s m<=n) (s≤s n<=p) = s≤s (≤-trans m<=n n<=p)
  
  mono₀ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
  mono₀ zero p q p<=q = p<=q
  mono₀ (suc n) p q p<=q = s≤s (mono₀ n p q p<=q)

  infix 4 _<_
  data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n : ℕ} → zero < suc n
    s<s : ∀ {m n : ℕ} → m < n → suc m < suc n
  
  le-trans : ∀ {n m p : ℕ} → n < m → m < p → n < p
  le-trans z<s (s<s m<p) = z<s
  le-trans (s<s n<m) (s<s m<p) = s<s (le-trans n<m m<p)

  ≤-iff-<₀  : ∀ {m n : ℕ} → suc m ≤ n → m < n
  ≤-iff-<₀ {m = zero} (s≤s sm<=n) = z<s
  ≤-iff-<₀ {m = suc m'} (s≤s sm<=n) = s<s (≤-iff-<₀ {m = m'} sm<=n)

  ≤-iff-<₁ : ∀ {m n : ℕ} → m < n → suc m ≤ n
  ≤-iff-<₁ {m = zero} z<s = s≤s (z≤n) 
  ≤-iff-<₁ {m = suc m'} (s<s m<n) = s≤s (≤-iff-<₁  {m = m'} m<n)
  
  data even : ℕ → Set
  data odd : ℕ → Set

  data even where
    ev0 : even zero
    evn : ∀ {n : ℕ} → odd n → even (suc n)
  
  data odd where
    odn : ∀ {n : ℕ} → even n → odd (suc n)
  
  e+e===e : ∀ {n m : ℕ} → even m → even n → even (m + n)
  o+e===o : ∀ {n m : ℕ} → odd m → even n → odd (m + n)

  e+e===e ev0 en = en
  e+e===e (evn oddm) en = evn (o+e===o oddm en)

  o+e===o (odn em) en = odn (e+e===e em en)

  -- o+o===e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
  -- o+o===e (odn em) on = evn (o+e===o on em)
  -- data Bool : Set where
  --   true : Bool
  --   false : Bool

  -- not : Bool -> Bool
  -- not true = false
  -- not false = true

  -- ∂ : Bool
  -- ∂ = not true

  -- _/\_ : (x : Bool) -> (y : Bool) -> Bool
  -- false /\ _ = false
  -- _ /\ false = false
  -- true /\ true = true

  -- data BoolProof : Set where
  --   short : {x : Bool} -> x ≡ false -> x /\ true ≡ false
  -- postulate plus-comm : (a b : Nat) -> a + b ≡ b + a
  -- postulate P : Nat -> Set

  -- thm : (a b : Nat) -> P (a + b) -> P (b + a)
  -- thm a b t with   a + b  | plus-comm a b
  -- thm a b t |    .(b + a) | refl = t

  -- data Fin : ℕ -> Set where
  --   fzero : {n : Nat} -> Fin (suc n)
  --   fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

  -- filter : {A : Set} → (A → Bool) → List A → List A
  -- filter p [] = []
  -- filter p (x ∷ xs) with p x
  -- ...                  | true  = x ∷ filter p xs
  -- ...                  | false = filter p xs

  -- data _⊆_ {A : Set} : List A → List A → Set where
  --   stop : [] ⊆ []
  --   drop : ∀ {x xs ys} → xs ⊆ ys →  xs ⊆ (x ∷ ys)
  --   keep : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
  
  -- ⊆-refl : {A : Set} {xs : List A} -> xs ⊆ xs
  -- ⊆-refl {xs = []} = stop
  -- ⊆-refl {xs = y ∷ ys} = keep (⊆-refl {xs = ys})

  -- ⊆-trans-lem : {A : Set}{xs : List A} → [] ⊆ xs
  -- ⊆-trans-lem {xs = []} = stop
  -- ⊆-trans-lem {xs = y ∷ ys} = drop (⊆-trans-lem {xs = ys})

  -- ⊆-trans : {A : Set}{xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  -- ⊆-trans stop _            = ⊆-trans-lem
  -- ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
  -- ⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
  -- ⊆-trans {ys = x₃ ∷ ys₂} {x₁ ∷ ys₁} (drop p)
  --   (drop {xs = x₃ ∷ ys₂} q) = drop (⊆-trans p q)
  -- ⊆-trans {xs = xs} {ys = x ∷ ys'} {zs = x ∷ ys} (drop p) (drop q) 
  --   = drop (⊆-trans {xs = xs}{ys = ys'}{zs = ys} p q)
  -- postulate Prop : ∀ {A} -> List A -> Set
  -- postulate p-nil : P []
  -- postulate Q : Set
  -- postulate q-nil : Q

  -- proof : {A : Set} -> (p : A -> Bool) -> (xs : List A) -> P (filter xs p)



  -- _o_ : {A : Set} {B : A -> Set} {C : (x : A) -> B x -> Set} -> (f : {x : A} -> (y : B x) -> C x y)
  --     -> (g : (x : A) -> B x) -> (x : A) -> C x (g x)
  -- (f o g) x = f (g x)

  -- plusOne : (n : Nat) -> Nat
  -- plusOne n = n + 1

  -- timesTwo : (n : Nat) -> Nat
  -- timesTwo x = x * 2

  -- data Maybe (A : Set) : Set where
  --   Just : A -> Maybe A
  --   Nothing : Maybe A


