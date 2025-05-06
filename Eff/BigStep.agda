open import Relation.Binary.PropositionalEquality

open import Eff.Syntax

module Eff.BigStep where

mutual
  Env : Context → Set
  Env Γ = ∀ {A} → Γ ∋ A → ClosedVal A

  data ClosedVal : ValType → Set where
  
    `tt :
        ------------
        ClosedVal `⊤
    
    `inj₁ :
        ClosedVal A₁
        -------------------
      → ClosedVal (A₁ `⊎ A₂)
    
    `inj₂ :
        ClosedVal A₂
        -------------------
      → ClosedVal (A₁ `⊎ A₂)
    
    `⟨_,_⟩ :
        ClosedVal A₁
      → ClosedVal A₂
        -------------------
      → ClosedVal (A₁ `× A₂)
    
    [｛_｝⨾_] :
        Γ ⊢c C
      → Env Γ
        ---------------
      → ClosedVal (𝑼 C)

_++_ : Env Γ → ClosedVal A → Env (Γ , A)
(γ ++ a) Z = a
(γ ++ a) (S x) = γ x

data ClosedTerminal : CompType → Set where

  return_ :
      ClosedVal A
      --------------------
    → ClosedTerminal (𝑭 A)
  
  [ƛ_⨾_] :
      Γ , A ⊢c C
    → Env Γ
      ---------------------
    → ClosedTerminal (A ⇒ C)
  
  [ƛ⟨_,_⟩⨾_] :
      Γ ⊢c C₁
    → Γ ⊢c C₂
    → Env Γ
      -----------------------
    → ClosedTerminal (C₁ & C₂)

infix 6 return_

data _⊢v_⇓_ : Env Γ → Γ ⊢v A → ClosedVal A → Set where

  ⇓v-var : ∀ {γ : Env Γ} {x : Γ ∋ A} {W : ClosedVal A}
    → γ x ≡ W
      ------------
    → γ ⊢v ` x ⇓ W
    
  ⇓v-tt : ∀ {γ : Env Γ}
      --------------
    → γ ⊢v `tt ⇓ `tt

  ⇓v-thunk : ∀ {γ : Env Γ} {M : Γ ⊢c C}
    → γ ⊢v ｛ M ｝ ⇓ [｛ M ｝⨾ γ ]

  ⇓v-pair : ∀ {γ : Env Γ}
              {V₁ : Γ ⊢v A₁} {W₁ : ClosedVal A₁}
              {V₂ : Γ ⊢v A₂} {W₂ : ClosedVal A₂}
    → γ ⊢v V₁ ⇓ W₁
    → γ ⊢v V₂ ⇓ W₂
      ------------------------------
    → γ ⊢v `⟨ V₁ , V₂ ⟩ ⇓ `⟨ W₁ , W₂ ⟩

  ⇓v-inj₁ : ∀ {A₂ : ValType} {γ : Env Γ} {V : Γ ⊢v A₁} {W : ClosedVal A₁}
    → γ ⊢v V ⇓ W
      -------------------------------
    → γ ⊢v `inj₁ {A₂ = A₂} V ⇓ `inj₁ W

  ⇓v-inj₂ : ∀ {A₁ : ValType} {γ : Env Γ} {V : Γ ⊢v A₂} {W : ClosedVal A₂}
    → γ ⊢v V ⇓ W
      -------------------------------
    → γ ⊢v `inj₂ {A₁ = A₁} V ⇓ `inj₂ W

data _⊢c_⇓_ : Env Γ → Γ ⊢c C → ClosedTerminal C → Set where

  ⇓c-abs : ∀ {γ : Env Γ} {M : Γ , A ⊢c C}
      --------------------
    → γ ⊢c ƛ M ⇓ [ƛ M ⨾ γ ]

  ⇓c-app : ∀ {γ γ′ : Env Γ}
             {M : Γ ⊢c A ⇒ C} {M′ : Γ , A ⊢c C}
             {V : Γ ⊢v A} {W : ClosedVal A}
             {T : ClosedTerminal C}
    → γ ⊢c M ⇓ [ƛ M′ ⨾ γ′ ]
    → γ ⊢v V ⇓ W
    → (γ′ ++ W) ⊢c M′ ⇓ T
      --------------
    → γ ⊢c M · V ⇓ T

  ⇓c-force : ∀ {γ γ′ : Env Γ}
               {V : Γ ⊢v 𝑼 C} {M : Γ ⊢c C}
               {T : ClosedTerminal C}
    → γ ⊢v V ⇓ [｛ M ｝⨾ γ′ ]
    → γ′ ⊢c M ⇓ T
      ----------------------
    → γ ⊢c V ! ⇓ T
