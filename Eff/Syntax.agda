open import Data.Nat hiding ( _! )
open import Data.Nat.Properties
open import Data.Bool hiding ( _<_ ; _<?_ )
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map) renaming ( _,_ to _,,_ )
open import Data.List renaming ( _++_ to _+++_ )
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary hiding ( _⇒_ )
open import Induction.WellFounded
open import Function using ( _$_ )

module Eff.Syntax where

data Sort : Set where
  Op   : Sort
  Eff  : Sort
  Val  : Sort
  Comp : Sort
  Hand : Sort

data Type : Sort → Set where
  -- Operations
  _↝_ : Type Val → Type Val → Type Op

  -- Effects
  ∅ : Type Eff
  _,_ : Type Eff → Type Op → Type Eff

  -- Values
  `⊤ : Type Val
  𝑼⟨_⟩ : Type Eff → Type Comp → Type Val
  _`×_ : Type Val → Type Val → Type Val
  _`⊎_ : Type Val → Type Val → Type Val

  -- Computations
  _⇒_ : Type Val → Type Comp → Type Comp
  𝑭 : Type Val → Type Comp
  _&_ : Type Comp → Type Comp → Type Comp

  -- Handlers
  _[_]⇛[_]_ : Type Val → Type Eff → Type Eff → Type Comp → Type Hand

OpType : Set
OpType = Type Op

Effect : Set
Effect = Type Eff

ValType : Set
ValType = Type Val

CompType : Set
CompType = Type Comp

HandType : Set
HandType = Type Hand

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

    op[_]_⟨ƛ_⟩ :
        A ↝ B ∈ E
      → Γ ⊢v A
      → Γ , B ⊢⟨ E ⟩c C
        -------------
      → Γ ⊢⟨ E ⟩c C

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

    op⇒ : ∀ {A′ B′ : ValType}
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
return-clause {E = E , _} (op⇒ _ h) = return-clause h

op-clause : ∀ {A′ B′ : ValType} {E : Effect}
  → A′ ↝ B′ ∈ E → Γ ⊢h A [ E ]⇛[ F ] C → Γ , A′ , 𝑼⟨ F ⟩ (B′ ⇒ C) ⊢⟨ F ⟩c C
op-clause {A′ = A′} {B′ = B′} {E = E , .(A′ ↝ B′)} Z (op⇒ M _) = M
op-clause {E = E , x} (S i) (op⇒ _ h) = op-clause i h
