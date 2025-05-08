module CBPV.Syntax where

mutual
  data ValType : Set where
    `⊤ : ValType
    𝑼 : CompType → ValType
    _`×_ : ValType → ValType → ValType
    _`⊎_ : ValType → ValType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType
    _&_ : CompType → CompType → CompType

variable A B A₁ B₁ A₂ B₂ : ValType
variable C D C₁ D₁ C₂ D₂ : CompType

infixr 7 _⇒_
infixl 8 _`×_
infixl 8 _`⊎_
infixl 8 _&_

data Context : Set where
  ∅   : Context
  _,_ : Context → ValType → Context

variable Γ Δ Γ₁ Δ₁ Γ₂ Δ₂ : Context

infixl 5 _,_

data _∋_ : Context → ValType → Set where

  Z :
      ---------
      Γ , A ∋ A

  S_ :
      Γ ∋ A
      ---------
    → Γ , B ∋ A

infix  4 _∋_

mutual
  data _⊢v_ : Context → ValType → Set where

    `_ :
        Γ ∋ A
        ------
      → Γ ⊢v A

    `tt :
        -------
        Γ ⊢v `⊤

    ｛_｝ :
        Γ ⊢c C
        --------
      → Γ ⊢v 𝑼 C

    `⟨_,_⟩ :
        Γ ⊢v A₁
      → Γ ⊢v A₂
        -----------
      → Γ ⊢v A₁ `× A₂

    `inj₁ :
        Γ ⊢v A₁
        ------------
      → Γ ⊢v A₁ `⊎ A₂

    `inj₂ :
        Γ ⊢v A₂
        ------------
      → Γ ⊢v A₁ `⊎ A₂

  data _⊢c_ : Context → CompType → Set where

    ƛ_ :
        Γ , A ⊢c C
        ----------------
      → Γ ⊢c A ⇒ C

    _·_ :
        Γ ⊢c A ⇒ C
      → Γ ⊢v A
        ----------
      → Γ ⊢c C

    _! :
        Γ ⊢v 𝑼 C
        --------
      → Γ ⊢c C
 
    _⨾_ :
        Γ ⊢v `⊤
      → Γ ⊢c C
        --------
      → Γ ⊢c C
 
    ƛ⟨_,_⟩ :
        Γ ⊢c C₁
      → Γ ⊢c C₂
        -----------
      → Γ ⊢c C₁ & C₂

    `proj₁ :
        Γ ⊢c C₁ & C₂
        ------------
      → Γ ⊢c C₁

    `proj₂ :
        Γ ⊢c C₁ & C₂
        ------------
      → Γ ⊢c C₂

    return_ :
        Γ ⊢v A
        --------
      → Γ ⊢c 𝑭 A

    `let :
        Γ ⊢v A
      → Γ , A ⊢c C
        ----------
      → Γ ⊢c C

    _to_ :
        Γ ⊢c 𝑭 A
      → Γ , A ⊢c C
        ----------
      → Γ ⊢c C

    case× :
        Γ ⊢v A₁ `× A₂
      → Γ , A₁ , A₂ ⊢c C
        ----------------
      → Γ ⊢c C

    case⊎ :
        Γ ⊢v A₁ `⊎ A₂
      → Γ , A₁ ⊢c C
      → Γ , A₂ ⊢c C
        -------------
      → Γ ⊢c C

infix  4 _⊢v_
infix  4 _⊢c_
infix 5 ƛ_
infix 6 _!
infixl 7 _⨾_
infix 6 return_
infixl 7 _·_
infix 9 `_
infixr 5 _to_
