open import Data.Nat hiding ( _! )
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Bool hiding ( _<_ ; _<?_ ; _≤_ ;  _≤?_ )
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map) renaming ( _,_ to _,,_ )
open import Data.List renaming ( _++_ to _+++_ )
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary hiding ( _⇒_ )
open import Relation.Binary.Construct.On
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded
open import Function using ( _$_ ; _on_ )

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
  size-e : Effect → ℕ
  size-e ∅ = 0
  size-e (E , A ↝ B) = size-e E ⊔ suc (size-v A) ⊔ suc (size-v B)

  size-v : ValType → ℕ
  size-v `⊤ = 0
  size-v (𝑼⟨ E ⟩ C) = size-e E ⊔ size-c C
  size-v (A₁ `× A₂) = size-v A₁ ⊔ size-v A₂
  size-v (A₁ `⊎ A₂) = size-v A₁ ⊔ size-v A₂

  size-c : CompType → ℕ
  size-c (A ⇒ C) = size-v A ⊔ size-c C
  size-c (𝑭 A) = size-v A
  size-c (C₁ & C₂) = size-c C₁ ⊔ size-c C₂

Type : Set
Type = Effect ⊎ (ValType ⊎ CompType)

size : Type → ℕ
size (inj₁ E) = size-e E
size (inj₂ (inj₁ A)) = size-v A
size (inj₂ (inj₂ C)) = size-c C

_⊰_ : Type → Type → Set
_⊰_ = _<_ on size

infix 4 _⊰_

⊰-wf : WellFounded _⊰_
⊰-wf = wellFounded size <-wellFounded

data _↝_∈_ : ValType → ValType → Effect → Set where

  Z :
      -----------------
      A ↝ B ∈ E , A ↝ B

  S_ : ∀ {A′ B′ : ValType}
    → A ↝ B ∈ E
      -------------------
    → A ↝ B ∈ E , A′ ↝ B′

infix 3 _↝_∈_

⊰-op-inp : A ↝ B ∈ E → inj₂ (inj₁ A) ⊰ inj₁ E
⊰-op-inp {A} {B} {E , A ↝ B} Z with size-v A | size-v B | size-e E
... | sA | sB | sE = m≤n⇒m≤n⊔o (suc sB) (m≤n⊔m sE (suc sA))
⊰-op-inp {A} {B} {E , A′ ↝ B′} (S x)
  with size-e E | size-v A′ | size-v B′ | ⊰-op-inp x
... | sE | sA′ | sB′ | ssA≤sE =
  let
    ssA≤sE⊔ssA′⊔sE⊔ssB′ =
      ≤-trans ssA≤sE (
        ≤-trans
          (≤-reflexive (sym (⊔-idem sE)))
          (⊔-mono-≤ (m≤m⊔n sE (suc sA′)) (m≤m⊔n sE (suc sB′)))
      )
    sE⊔ssA′⊔sE⊔ssB′≤sE⊔ssA′⊔ssB′ =
      ≤-reflexive (
        subst
          (λ x → x ⊔ (sE ⊔ suc sB′) ≡ x ⊔ suc sB′)
          (⊔-comm (suc sA′) sE)
          (sym (⊔-triangulate (suc sA′) sE (suc sB′)))
      )
  in ≤-trans ssA≤sE⊔ssA′⊔sE⊔ssB′ sE⊔ssA′⊔sE⊔ssB′≤sE⊔ssA′⊔ssB′

⊰-op-out : A ↝ B ∈ E → inj₂ (inj₁ B) ⊰ inj₁ E
⊰-op-out {A} {B} {E , A ↝ B} Z with size-v A | size-v B | size-e E
... | sA | sB | sE = m≤n⊔m (sE ⊔ suc sA) (suc sB)
⊰-op-out {A} {B} {E , A′ ↝ B′} (S x)
 with size-e E | size-v A′ | size-v B′ | ⊰-op-out x
... | sE | sA′ | sB′ | ssB≤sE =
  let
    ssB≤sE⊔ssA′⊔sE⊔ssB′ =
      ≤-trans ssB≤sE (
        ≤-trans
          (≤-reflexive (sym (⊔-idem sE)))
          (⊔-mono-≤ (m≤m⊔n sE (suc sA′)) (m≤m⊔n sE (suc sB′)))
      )
    sE⊔ssA′⊔sE⊔ssB′≤sE⊔ssA′⊔ssB′ =
      ≤-reflexive (
        subst
          (λ x → x ⊔ (sE ⊔ suc sB′) ≡ x ⊔ suc sB′)
          (⊔-comm (suc sA′) sE)
          (sym (⊔-triangulate (suc sA′) sE (suc sB′)))
      )
  in ≤-trans ssB≤sE⊔ssA′⊔sE⊔ssB′ sE⊔ssA′⊔sE⊔ssB′≤sE⊔ssA′⊔ssB′

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
