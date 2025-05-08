module Eff.Syntax where

mutual
  record OpType : Set where
    inductive
    constructor _↝_
    field
      inp : ValType
      out : ValType

  data Effect : Set where
    ∅ : Effect
    _,_ : Effect → OpType → Effect

  data ValType : Set where
    `⊤ : ValType
    𝑼⟨_⟩ : Effect → CompType → ValType
    _`×_ : ValType → ValType → ValType
    _`⊎_ : ValType → ValType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType
    _&_ : CompType → CompType → CompType

  data HandType : Set where
    _[_]⇛[_]_ : ValType → Effect → Effect → CompType → HandType

variable O O₁ O₂ : OpType
variable E F E₁ F₁ E₂ F₂ : Effect
variable A B A₁ B₁ A₂ B₂ : ValType
variable C D C₁ D₁ C₂ D₂ : CompType
variable H H₁ H₂ : HandType

infix  7 _↝_
infixr 7 _⇒_
infixl 8 _`×_
infixl 8 _`⊎_
infixl 8 _&_

data _↝_∈_ : ValType → ValType → Effect → Set where

  Z :
      -----------------
      A ↝ B ∈ E , A ↝ B

  S_ : ∀ {A′ B′ : ValType}
    → A ↝ B ∈ E
      -------------------
    → A ↝ B ∈ E , A′ ↝ B′

infix 3 _↝_∈_

data Context : Set where
  ∅   : Context
  _,_ : Context → ValType → Context

variable Γ Δ Γ₁ Δ₁ Γ₂ Δ₂ : Context

_++_ : Context → Context → Context
Γ ++ ∅ = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

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
        Γ ⊢⟨ E ⟩c C
        -------------
      → Γ ⊢v 𝑼⟨ E ⟩ C

    `⟨_,_⟩ :
        Γ ⊢v A₁
      → Γ ⊢v A₂
        -------------
      → Γ ⊢v A₁ `× A₂

    `inj₁ :
        Γ ⊢v A₁
        -------------
      → Γ ⊢v A₁ `⊎ A₂

    `inj₂ :
        Γ ⊢v A₂
        -------------
      → Γ ⊢v A₁ `⊎ A₂

  data _⊢⟨_⟩c_ : Context → Effect → CompType → Set where

    op :
        A ↝ B ∈ E
      → Γ ⊢v A
        -------------
      → Γ ⊢⟨ E ⟩c 𝑭 B

    `with_handle_ :
        Γ ⊢h A [ E ]⇛[ F ] C
      → Γ ⊢⟨ E ⟩c 𝑭 A
        --------------------
      → Γ ⊢⟨ F ⟩c C

    ƛ_ :
        Γ , A ⊢⟨ E ⟩c C
        ---------------
      → Γ ⊢⟨ E ⟩c A ⇒ C

    _·_ :
        Γ ⊢⟨ E ⟩c A ⇒ C
      → Γ ⊢v A
        ---------------
      → Γ ⊢⟨ E ⟩c C

    _! :
        Γ ⊢v 𝑼⟨ E ⟩ C
        -------------
      → Γ ⊢⟨ E ⟩c C
 
    _⨾_ :
        Γ ⊢v `⊤
      → Γ ⊢⟨ E ⟩c C
        -----------
      → Γ ⊢⟨ E ⟩c C
 
    ƛ⟨_,_⟩ :
        Γ ⊢⟨ E ⟩c C₁
      → Γ ⊢⟨ E ⟩c C₂
        -----------------
      → Γ ⊢⟨ E ⟩c C₁ & C₂

    `proj₁ :
        Γ ⊢⟨ E ⟩c C₁ & C₂
        -----------------
      → Γ ⊢⟨ E ⟩c C₁

    `proj₂ :
        Γ ⊢⟨ E ⟩c C₁ & C₂
        -----------------
      → Γ ⊢⟨ E ⟩c C₂

    return_ :
        Γ ⊢v A
        -------------
      → Γ ⊢⟨ E ⟩c 𝑭 A

    `let :
        Γ ⊢v A
      → Γ , A ⊢⟨ E ⟩c C
        ---------------
      → Γ ⊢⟨ E ⟩c C

    _to_ :
        Γ ⊢⟨ E ⟩c 𝑭 A
      → Γ , A ⊢⟨ E ⟩c C
        ---------------
      → Γ ⊢⟨ E ⟩c C

    case× :
        Γ ⊢v A₁ `× A₂
      → Γ , A₁ , A₂ ⊢⟨ E ⟩c C
        ---------------------
      → Γ ⊢⟨ E ⟩c C

    case⊎ :
        Γ ⊢v A₁ `⊎ A₂
      → Γ , A₁ ⊢⟨ E ⟩c C
      → Γ , A₂ ⊢⟨ E ⟩c C
        ----------------
      → Γ ⊢⟨ E ⟩c C

  data _⊢h_ : Context → HandType → Set where

    return⇒ :
        Γ , A ⊢⟨ F ⟩c C
        --------------------
      → Γ ⊢h A [ ∅ ]⇛[ F ] C

    op⇛ : ∀ {A′ B′ : ValType}
      → Γ , A′ , 𝑼⟨ F ⟩ (B′ ⇒ C) ⊢⟨ F ⟩c C
      → Γ ⊢h A [ E ]⇛[ F ] C
        ----------------------------------
      → Γ ⊢h A [ E , A′ ↝ B′ ]⇛[ F ] C

infix  4 _⊢v_
infix  4 _⊢⟨_⟩c_
infix  4 _⊢h_
infix 5 ƛ_
infix 6 _!
infixl 7 _⨾_
infix 6 return_
infixl 7 _·_
infix 9 `_
infixr 5 _to_

return-clause : ∀ {E : Effect} → Γ ⊢h A [ E ]⇛[ F ] C → Γ , A ⊢⟨ F ⟩c C
return-clause {E = ∅} (return⇒ M) = M
return-clause {E = E , _} (op⇛ _ h) = return-clause h

op-clause : ∀ {A′ B′ : ValType} {E : Effect}
  → A′ ↝ B′ ∈ E → Γ ⊢h A [ E ]⇛[ F ] C → Γ , A′ , 𝑼⟨ F ⟩ (B′ ⇒ C) ⊢⟨ F ⟩c C
op-clause {A′ = A′} {B′ = B′} {E = E , .(A′ ↝ B′)} Z (op⇛ M _) = M
op-clause {E = E , x} (S i) (op⇛ _ h) = op-clause i h

mutual
  ext-var : Γ ++ Δ ∋ A → (Γ , B) ++ Δ ∋ A
  ext-var {Δ = ∅} x = S x
  ext-var {Δ = Δ , A} Z = Z
  ext-var {Δ = Δ , A} (S x) = S ext-var x
 
  ext-val : Γ ++ Δ ⊢v A → (Γ , B) ++ Δ ⊢v A
  ext-val {Δ = Δ} (` x) = ` ext-var x
  ext-val `tt = `tt
  ext-val ｛ M ｝ = ｛ ext-comp M ｝
  ext-val `⟨ V₁ , V₂ ⟩ = `⟨ ext-val V₁ , ext-val V₂ ⟩
  ext-val (`inj₁ V) = `inj₁ (ext-val V)
  ext-val (`inj₂ V) = `inj₂ (ext-val V)

  ext-comp : Γ ++ Δ ⊢⟨ E ⟩c C → (Γ , B) ++ Δ ⊢⟨ E ⟩c C
  ext-comp (op i V) = op i (ext-val V)
  ext-comp (`with H handle M) = `with ext-hand H handle ext-comp M
  ext-comp {Γ = Γ} {Δ = Δ} {B = B} (ƛ_ {A = A} M) =
    ƛ ext-comp {Γ = Γ} {Δ = Δ , A} {B = B} M
  ext-comp (M · V) = ext-comp M · ext-val V
  ext-comp (V !) = ext-val V !
  ext-comp (V ⨾ M) = ext-val V ⨾ ext-comp M
  ext-comp ƛ⟨ M₁ , M₂ ⟩ = ƛ⟨ ext-comp M₁ , ext-comp M₂ ⟩
  ext-comp (`proj₁ M) = `proj₁ (ext-comp M)
  ext-comp (`proj₂ M) = `proj₂ (ext-comp M)
  ext-comp (return V) = return (ext-val V)
  ext-comp {Γ = Γ} {Δ = Δ} {B = B} (`let {A = A} V M) =
    `let (ext-val V) (ext-comp {Γ = Γ} {Δ = Δ , A} {B = B} M)
  ext-comp {Γ = Γ} {Δ = Δ} {B = B} (_to_ {A = A} M N) =
    (ext-comp M) to (ext-comp {Γ = Γ} {Δ = Δ , A} {B = B} N)
  ext-comp {Γ = Γ} {Δ = Δ} {B = B} (case× {A₁ = A₁} {A₂ = A₂} V M) =
    case× (ext-val V) (ext-comp {Γ = Γ} {Δ = Δ , A₁ , A₂} {B = B} M)
  ext-comp {Γ = Γ} {Δ = Δ} {B = B} (case⊎ {A₁ = A₁} {A₂ = A₂} V M₁ M₂) =
    case⊎ (ext-val V)
      (ext-comp {Γ = Γ} {Δ = Δ , A₁} {B = B} M₁)
      (ext-comp {Γ = Γ} {Δ = Δ , A₂} {B = B} M₂)

  ext-hand : Γ ++ Δ ⊢h A [ E ]⇛[ F ] C → (Γ , B) ++ Δ ⊢h A [ E ]⇛[ F ] C
  ext-hand {Γ = Γ} {Δ = Δ} {A = A} {B = B} (return⇒ M) =
    return⇒ (ext-comp {Γ = Γ} {Δ = Δ , A} {B = B} M)
  ext-hand {Γ} {Δ} {A} {E} {F} {C} {B} (op⇛ {A′ = A′} {B′ = B′} M H) =
    op⇛ (ext-comp {Γ = Γ} {Δ = Δ ,  A′ , 𝑼⟨ F ⟩ (B′ ⇒ C)} {B = B} M) (ext-hand H)
