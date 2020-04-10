module plfa.part2.Lambda where
    open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
    open import Data.String using (String; _≟_)
    open import Data.Nat using (ℕ; zero; suc)
    open import Data.Empty using (⊥; ⊥-elim)
    open import Relation.Nullary using (Dec; yes; no; ¬_)
    open import Data.List using (List; _∷_; [])

    Id : Set
    Id = String

    infix  5  ƛ_⇒_
    infix  5  μ_⇒_
    infixl 7  _·_
    infix  8  `suc_
    infix  9  `_

    data Term : Set where
        `_                      :  Id → Term
        ƛ_⇒_                    :  Id → Term → Term
        _·_                     :  Term → Term → Term
        `zero                   :  Term
        `suc_                   :  Term → Term
        case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
        μ_⇒_                    :  Id → Term → Term

    two : Term
    two = `suc `suc `zero

    plus : Term
    plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
             case ` "m"
                [zero⇒ ` "n"
                |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

    twoᶜ : Term
    twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

    plusᶜ : Term
    plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
            ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

    sucᶜ : Term
    sucᶜ = ƛ "n" ⇒ `suc (` "n")

    -- Exercise mul
    mul : Term
    mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
             case ` "m"
                [zero⇒ `zero
                |suc "m" ⇒ ` "+" · ` "n" · (` "*" · ` "m" · ` "n") ]

    -- Exercise mulᶜ
    mulᶜ : Term
    mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
            ` "m" · (` "n" · ` "s" · ` "z")

    -- Exercise primed
    ƛ′_⇒_ : Term → Term → Term
    ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
    ƛ′ _ ⇒ _      =  ⊥-elim impossible
        where postulate impossible : ⊥

    case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
    case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
    case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
        where postulate impossible : ⊥

    μ′_⇒_ : Term → Term → Term
    μ′ (` x) ⇒ N  =  μ x ⇒ N
    μ′ _ ⇒ _      =  ⊥-elim impossible
        where postulate impossible : ⊥

    plus′ : Term
    plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
        where
        +  =  ` "+"
        m  =  ` "m"
        n  =  ` "n"

    mul′ : Term
    mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ `zero
            |suc m ⇒ + · n · (* · m · n) ]
        where
            + = ` "+"
            * = ` "*"
            m = ` "m"
            n = ` "n"

    data Value : Term → Set where
        V-ƛ : ∀ {x N}
            ---------------
            → Value (ƛ x ⇒ N)

        V-zero :
            -----------
            Value `zero

        V-suc : ∀ {V}
            → Value V
            --------------
            → Value (`suc V)

    infix 9 _[_:=_]

    _[_:=_] : Term → Id → Term → Term
    subst : Term → Id → Term → Term
    subst L x r = L [ x := r ]
    (` x) [ y := V ] with x ≟ y
    ... | yes _          =  V
    ... | no  _          =  ` x

    (ƛ x ⇒ N) [ y := V ] with x ≟ y
    ... | yes _          =  ƛ x ⇒ N
    ... | no  _          =  ƛ x ⇒ subst N y V

    (L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
    (`zero) [ y := V ]   =  `zero
    (`suc M) [ y := V ]  =  `suc M [ y := V ]

    (case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
    ... | yes _          =  case (subst L y V) [zero⇒ M [ y := V ] |suc x ⇒ N ]
    ... | no  _          =  case (subst L y V) [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]

    (μ x ⇒ N) [ y := V ] with x ≟ y
    ... | yes _          =  μ x ⇒ N
    ... | no  _          =  μ x ⇒ N [ y := V ]

    _ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
    _ = refl

    -- Reduction
    infix 4 _—→_

    data _—→_ : Term → Term → Set where
      ξ—·₁ : ∀ {L L' M} →
                    L —→ L' →
                    ---------------
                    L · M —→ L' · M
      ξ—·₂ : ∀ {V M M'} →
                    Value V →
                    M —→ M' →
                    ----------------
                    V · M —→ V · M'
      β—ƛ  : ∀ {x N V} →
                    Value V →
                    -----------------------------
                    (ƛ x ⇒ N) · V —→ N [ x := V ]

      ξ-suc : ∀ {M M′}
              → M —→ M′
                ------------------
              → `suc M —→ `suc M′

      ξ-case : ∀ {x L L′ M N}
              → L —→ L′
                -----------------------------------------------------------------
              → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

      β-zero : ∀ {x M N}
                ----------------------------------------
              → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

      β-suc : ∀ {x V M N}
              → Value V
                ---------------------------------------------------
              → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

      β-μ : ∀ {x M}
                ------------------------------
              → μ x ⇒ M —→ M [ x := μ x ⇒ M ]


    infix  2 _—↠_
    infix  1 begin_
    infixr 2 _—→⟨_⟩_
    infix  3 _∎

    data _—↠_ : Term → Term → Set where
      _∎ : ∀ M
          ---------
        → M —↠ M

      _—→⟨_⟩_ : ∀ L {M N}
        → L —→ M
        → M —↠ N
          ---------
        → L —↠ N

    begin_ : ∀ {M N}
      → M —↠ N
        ------
      → M —↠ N
    begin M—↠N = M—↠N

    infixr 7 _⇒_

    data Type : Set where
      _⇒_ : Type → Type → Type
      `ℕ : Type

    infixl 5  _,_⦂_
    data Context : Set where
      ∅     : Context
      _,_⦂_ : Context → Id → Type → Context

    infix  4  _∋_⦂_
    data _∋_⦂_ : Context → Id → Type → Set where
      Z : ∀ {Γ x A}
          ------------------
        → Γ , x ⦂ A ∋ x ⦂ A

      S : ∀ {Γ x y A B}
        → x ≢ y
        → Γ ∋ x ⦂ A
          ------------------
        → Γ , y ⦂ B ∋ x ⦂ A
