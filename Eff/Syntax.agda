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

mutual
  size : Effect → ℕ
  size ∅ = 0
  size (E , A ↝ B) = size E ⊔ size-v A ⊔ size-v B

  size-v : ValType → ℕ
  size-v `⊤ = 0
  size-v (𝑼⟨ E ⟩ C) = suc $ size E ⊔ size-c C
  size-v (A₁ `× A₂) = size-v A₁ ⊔ size-v A₂
  size-v (A₁ `⊎ A₂) = size-v A₁ ⊔ size-v A₂

  size-c : CompType → ℕ
  size-c (A ⇒ C) = size-v A ⊔ size-c C
  size-c (𝑭 A) = size-v A
  size-c (C₁ & C₂) = size-c C₁ ⊔ size-c C₂

-- _<e_ : Effect → Effect → Set
-- E₁ <e E₂ = True (size E₁ <? size E₂)

-- _<v_ : ValType → ValType → Set
-- A₁ <v A₂ = True (size-v A₁ <? size-v A₂)

-- _<c_ : CompType → CompType → Set
-- C₁ <c C₂ = True (size-c C₁ <? size-c C₂)

mutual
  data _<e_ : Effect → Effect → Set where
    <e-base :          ∅ <e (E , A ↝ B)
    <e-inp  : E <v A → E <e (F , A ↝ B)
    <e-out  : E <v B → E <e (F , A ↝ B)
    <e-rec  : E <e F → E <e (F , A ↝ B)

  data _<v_ : Effect → ValType → Set where
    <v-thunk-eq   :           E <v 𝑼⟨ E ⟩ C
    <v-thunk-rec  : E <e F  → E <v 𝑼⟨ F ⟩ C
    <v-thunk-comp : E <c C  → E <v (𝑼⟨ F ⟩ C)
    <v-prod₁      : E <v A₁ → E <v (A₁ `× A₂)
    <v-prod₂      : E <v A₂ → E <v (A₁ `× A₂)
    <v-sum₁       : E <v A₁ → E <v (A₁ `⊎ A₂)
    <v-sum₂       : E <v A₂ → E <v (A₁ `⊎ A₂)

  data _<c_ : Effect → CompType → Set where
    <c-fun-dom : E <v A  → E <c (A ⇒ C)
    <c-fun-cod : E <c C  → E <c (A ⇒ C)
    <c-free    : E <v A → E <c (𝑭 A)
    <c-prod₁   : E <c C₁ → E <c (C₁ & C₂)
    <c-prod₂   : E <c C₂ → E <c (C₁ & C₂)

-- data _<es_ : Effect → Effect → Set where
--   <es-base :                                        ∅ <es (E , A ↝ B)
--   <es-¬i¬o : ¬ (E <v A) → ¬ (E <v B) →    E <e F  → E <es (F , A ↝ B)
--   <es-¬i¬r : ¬ (E <v A) →    E <v B  → ¬ (E <e F) → E <es (F , A ↝ B)
--   <es-¬o¬r :    E <v A  → ¬ (E <v B) → ¬ (E <e F) → E <es (F , A ↝ B)
--   <es-¬i   : ¬ (E <v A) →    E <v B  →    E <e F  → E <es (F , A ↝ B)
--   <es-¬o   :    E <v A  → ¬ (E <v B) →    E <e F  → E <es (F , A ↝ B)
--   <es-¬r   :    E <v A  →    E <v B  → ¬ (E <e F) → E <es (F , A ↝ B)
--   <es-all  :    E <v A  →    E <v B  →    E <e F  → E <es (F , A ↝ B)

mutual
  get-sub-effects : ∀ E → List (∃[ F ] (F <e E))
  get-sub-effects ∅ = []
  get-sub-effects F@(_ , _ ↝ _) = (∅ ,, <e-base) ∷ (get-sub-effects-aux F) 

  get-sub-effects-aux : ∀ E → List (∃[ F ] (F <e E))
  get-sub-effects-aux ∅ = []
  get-sub-effects-aux (E , A ↝ B) =
    map (λ (x ,, y) → x ,, <e-rec y) (get-sub-effects-aux E) +++
    map (λ (x ,, y) → x ,, <e-inp y) (get-sub-effects-v A) +++
    map (λ (x ,, y) → x ,, <e-out y) (get-sub-effects-v B)

  get-sub-effects-v : ∀ A → List (∃[ F ] (F <v A))
  get-sub-effects-v `⊤ = []
  get-sub-effects-v (𝑼⟨ E ⟩ C) =
    (E ,, <v-thunk-eq) ∷ (
      map (λ (x ,, y) → x ,, <v-thunk-rec y) (get-sub-effects-aux E) +++
      map (λ (x ,, y) → x ,, <v-thunk-comp y) (get-sub-effects-c C)
    )
  get-sub-effects-v (A₁ `× A₂) =
    map (λ (x ,, y) → x ,, <v-prod₁ y) (get-sub-effects-v A₁) +++
    map (λ (x ,, y) → x ,, <v-prod₂ y) (get-sub-effects-v A₂)
  get-sub-effects-v (A₁ `⊎ A₂) =
    map (λ (x ,, y) → x ,, <v-sum₁ y) (get-sub-effects-v A₁) +++
    map (λ (x ,, y) → x ,, <v-sum₂ y) (get-sub-effects-v A₂)

  get-sub-effects-c : ∀ C → List (∃[ F ] (F <c C))
  get-sub-effects-c (A ⇒ C) =
    map (λ (x ,, y) → x ,, <c-fun-dom y) (get-sub-effects-v A) +++
    map (λ (x ,, y) → x ,, <c-fun-cod y) (get-sub-effects-c C)
  get-sub-effects-c (𝑭 A) =
    map (λ (x ,, y) → x ,, <c-free y) (get-sub-effects-v A)
  get-sub-effects-c (C₁ & C₂) =
    map (λ (x ,, y) → x ,, <c-prod₁ y) (get-sub-effects-c C₁) +++
    map (λ (x ,, y) → x ,, <c-prod₂ y) (get-sub-effects-c C₂)

mutual
  <v-<v-inp : E <v A₁ → (F , A₁ ↝ B₁) <v A → E <v A
  <v-<v-inp x <v-thunk-eq = <v-thunk-rec (<e-inp x)
  <v-<v-inp x (<v-thunk-rec y) = <v-thunk-rec (<e-trans (<e-inp x) y)
  <v-<v-inp x (<v-thunk-comp y) = <v-thunk-comp (<v-<c-inp x y)
  <v-<v-inp x (<v-prod₁ y) = <v-prod₁ (<v-<v-inp x y)
  <v-<v-inp x (<v-prod₂ y) = <v-prod₂ (<v-<v-inp x y)
  <v-<v-inp x (<v-sum₁ y) = <v-sum₁ (<v-<v-inp x y)
  <v-<v-inp x (<v-sum₂ y) = <v-sum₂ (<v-<v-inp x y)

  <v-<c-inp : E <v A₁ → (F , A₁ ↝ B₁) <c C → E <c C
  <v-<c-inp x (<c-fun-dom y) = <c-fun-dom (<v-<v-inp x y)
  <v-<c-inp x (<c-fun-cod y) = <c-fun-cod (<v-<c-inp x y)
  <v-<c-inp x (<c-free y) = <c-free (<v-<v-inp x y)
  <v-<c-inp x (<c-prod₁ y) = <c-prod₁ (<v-<c-inp x y)
  <v-<c-inp x (<c-prod₂ y) = <c-prod₂ (<v-<c-inp x y)

  <v-<v-out : E <v B₁ → (F , A₁ ↝ B₁) <v A → E <v A
  <v-<v-out x <v-thunk-eq = <v-thunk-rec (<e-out x)
  <v-<v-out x (<v-thunk-rec y) = <v-thunk-rec (<e-trans (<e-out x) y)
  <v-<v-out x (<v-thunk-comp y) = <v-thunk-comp (<v-<c-out x y)
  <v-<v-out x (<v-prod₁ y) = <v-prod₁ (<v-<v-out x y)
  <v-<v-out x (<v-prod₂ y) = <v-prod₂ (<v-<v-out x y)
  <v-<v-out x (<v-sum₁ y) = <v-sum₁ (<v-<v-out x y)
  <v-<v-out x (<v-sum₂ y) = <v-sum₂ (<v-<v-out x y)

  <v-<c-out : E <v B₁ → (F , A₁ ↝ B₁) <c C → E <c C
  <v-<c-out x (<c-fun-dom y) = <c-fun-dom (<v-<v-out x y)
  <v-<c-out x (<c-fun-cod y) = <c-fun-cod (<v-<c-out x y)
  <v-<c-out x (<c-free y) = <c-free (<v-<v-out x y)
  <v-<c-out x (<c-prod₁ y) = <c-prod₁ (<v-<c-out x y)
  <v-<c-out x (<c-prod₂ y) = <c-prod₂ (<v-<c-out x y)

  <e-<v-aux : E <e F → (F , A₁ ↝ B₁) <v A → E <v A
  <e-<v-aux x <v-thunk-eq = <v-thunk-rec (<e-rec x)
  <e-<v-aux x (<v-thunk-rec y) = <v-thunk-rec (<e-trans (<e-rec x) y)
  <e-<v-aux x (<v-thunk-comp y) = <v-thunk-comp (<e-<c-aux x y)
  <e-<v-aux x (<v-prod₁ y) = <v-prod₁ (<e-<v-aux x y)
  <e-<v-aux x (<v-prod₂ y) = <v-prod₂ (<e-<v-aux x y)
  <e-<v-aux x (<v-sum₁ y) = <v-sum₁ (<e-<v-aux x y)
  <e-<v-aux x (<v-sum₂ y) = <v-sum₂ (<e-<v-aux x y)

  <e-<c-aux : E <e F → (F , A₁ ↝ B₁) <c C → E <c C
  <e-<c-aux x (<c-fun-dom y) = <c-fun-dom (<e-<v-aux x y)
  <e-<c-aux x (<c-fun-cod y) = <c-fun-cod (<e-<c-aux x y)
  <e-<c-aux x (<c-free y) = <c-free (<e-<v-aux x y)
  <e-<c-aux x (<c-prod₁ y) = <c-prod₁ (<e-<c-aux x y)
  <e-<c-aux x (<c-prod₂ y) = <c-prod₂ (<e-<c-aux x y)
  
  <e-trans : ∀ {E₁ E₂ E₃} → E₁ <e E₂ → E₂ <e E₃ → E₁ <e E₃
  <e-trans <e-base    (<e-inp _) = <e-base
  <e-trans <e-base    (<e-out _) = <e-base
  <e-trans (<e-inp x) (<e-inp y) = <e-inp (<v-<v-inp x y)
  <e-trans (<e-inp x) (<e-out y) = <e-out (<v-<v-inp x y)
  <e-trans (<e-out x) (<e-inp y) = <e-inp (<v-<v-out x y)
  <e-trans (<e-out x) (<e-out y) = <e-out (<v-<v-out x y)
  <e-trans (<e-rec x) (<e-inp y) = <e-inp (<e-<v-aux x y)
  <e-trans (<e-rec x) (<e-out y) = <e-out (<e-<v-aux x y)
  <e-trans x          (<e-rec y) = <e-rec (<e-trans x y)

mutual
  <e-<v : E <e F → F <v A → E <v A
  <e-<v x <v-thunk-eq = <v-thunk-rec x
  <e-<v x (<v-thunk-rec y) = <v-thunk-rec (<e-trans x y)
  <e-<v x (<v-thunk-comp y) = <v-thunk-comp (<e-<c x y)
  <e-<v x (<v-prod₁ y) = <v-prod₁ (<e-<v x y)
  <e-<v x (<v-prod₂ y) = <v-prod₂ (<e-<v x y)
  <e-<v x (<v-sum₁ y) = <v-sum₁ (<e-<v x y)
  <e-<v x (<v-sum₂ y) = <v-sum₂ (<e-<v x y)

  <e-<c : E <e F → F <c C → E <c C
  <e-<c x (<c-fun-dom y) = <c-fun-dom (<e-<v x y)
  <e-<c x (<c-fun-cod y) = <c-fun-cod (<e-<c x y)
  <e-<c x (<c-free y) = <c-free (<e-<v x y)
  <e-<c x (<c-prod₁ y) = <c-prod₁ (<e-<c x y)
  <e-<c x (<c-prod₂ y) = <c-prod₂ (<e-<c x y)

-- wf-<e : WellFounded _<e_
-- wf-<e E = acc (go E)
--   where
--   go : ∀ F → WfRec _<e_ (Acc _<e_) F
--   go F₂ {F₁} <e-base = acc λ ()
--   go (F₂ , A ↝ B) {F₁} (<e-inp x) = {!!}
--   go (F₂ , A ↝ B) {F₁} (<e-out x) = acc λ {F₃} y → let z = <e-<v y x in go F₂ {!!}
--   go (F₂ , A ↝ B) {F₁} (<e-rec x) = acc λ {F₃} y → go F₂ (<e-trans y x)

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
