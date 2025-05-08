open import Relation.Binary.PropositionalEquality

open import CBPV.Syntax

module CBPV.BigStep where

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

infixl 6 _++_

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

  ⇓c-app : ∀ {γ : Env Γ} {δ : Env Δ}
             {M : Γ ⊢c A ⇒ C} {N : Δ , A ⊢c C}
             {V : Γ ⊢v A} {W : ClosedVal A}
             {T : ClosedTerminal C}
    → γ ⊢c M ⇓ [ƛ N ⨾ δ ]
    → γ ⊢v V ⇓ W
    → (δ ++ W) ⊢c N ⇓ T
      --------------
    → γ ⊢c M · V ⇓ T

  ⇓c-force : ∀ {γ : Env Γ} {δ : Env Δ}
               {V : Γ ⊢v 𝑼 C} {M : Δ ⊢c C}
               {T : ClosedTerminal C}
    → γ ⊢v V ⇓ [｛ M ｝⨾ δ ]
    → δ ⊢c M ⇓ T
      ----------------------
    → γ ⊢c V ! ⇓ T

  ⇓c-seq : ∀ {γ : Env Γ}
             {V : Γ ⊢v `⊤}
             {M : Γ ⊢c C} {T : ClosedTerminal C}
    → γ ⊢v V ⇓ `tt
    → γ ⊢c M ⇓ T
      --------------
    → γ ⊢c V ⨾ M ⇓ T

  ⇓c-pair : ∀ {γ : Env Γ}
              {M₁ : Γ ⊢c C₁} {M₂ : Γ ⊢c C₂}
      --------------------
    → γ ⊢c ƛ⟨ M₁ , M₂ ⟩ ⇓ [ƛ⟨ M₁ , M₂ ⟩⨾ γ ]

  ⇓c-proj₁ : ∀ {γ : Env Γ} {δ : Env Δ}
               {M : Γ ⊢c C₁ & C₂} {M₁ : Δ ⊢c C₁} {M₂ : Δ ⊢c C₂}
               {T : ClosedTerminal C₁}
    → γ ⊢c M ⇓ [ƛ⟨ M₁ , M₂ ⟩⨾ δ ]
    → δ ⊢c M₁ ⇓ T
      ----------------------------
    → γ ⊢c `proj₁ M ⇓ T

  ⇓c-proj₂ : ∀ {γ : Env Γ} {δ : Env Δ}
               {M : Γ ⊢c C₁ & C₂} {M₁ : Δ ⊢c C₁} {M₂ : Δ ⊢c C₂}
               {T : ClosedTerminal C₂}
    → γ ⊢c M ⇓ [ƛ⟨ M₁ , M₂ ⟩⨾ δ ]
    → δ ⊢c M₂ ⇓ T
      ----------------------------
    → γ ⊢c `proj₂ M ⇓ T

  ⇓c-return : ∀ {γ : Env Γ}
                {V : Γ ⊢v A} {W : ClosedVal A}
    → γ ⊢v V ⇓ W
      ----------------------------
    → γ ⊢c (return V) ⇓ (return W)

  ⇓c-let : ∀ {γ : Env Γ}
             {V : Γ ⊢v A} {W : ClosedVal A}
             {M : Γ , A ⊢c C} {T : ClosedTerminal C}
    → γ ⊢v V ⇓ W
    → (γ ++ W) ⊢c M ⇓ T
      -----------------
    → γ ⊢c `let V M ⇓ T

  ⇓c-to : ∀ {γ : Env Γ}
            {M : Γ ⊢c 𝑭 A} {W : ClosedVal A}
            {N : Γ , A ⊢c C} {T : ClosedTerminal C}
    → γ ⊢c M ⇓ (return W)
    → (γ ++ W) ⊢c N ⇓ T
      -----------------
    → γ ⊢c M to N ⇓ T

  ⇓c-case× : ∀ {γ : Env Γ}
               {V : Γ ⊢v A₁ `× A₂} {W₁ : ClosedVal A₁} {W₂ : ClosedVal A₂}
               {M : Γ , A₁ , A₂ ⊢c C } {T : ClosedTerminal C}
    → γ ⊢v V ⇓ `⟨ W₁ , W₂ ⟩
    → (γ ++ W₁ ++ W₂) ⊢c M ⇓ T
      ------------------------
    → γ ⊢c case× V M ⇓ T

  ⇓c-case⊎-inj₁ : ∀ {γ : Env Γ}
                    {V : Γ ⊢v A₁ `⊎ A₂} {W : ClosedVal A₁}
                    {M₁ : Γ , A₁ ⊢c C} {M₂ : Γ , A₂ ⊢c C} {T : ClosedTerminal C}
    → γ ⊢v V ⇓ `inj₁ W
    → (γ ++ W) ⊢c M₁ ⇓ T
      ---------------------
    → γ ⊢c case⊎ V M₁ M₂ ⇓ T

  ⇓c-case⊎-inj₂ : ∀ {γ : Env Γ}
                    {V : Γ ⊢v A₁ `⊎ A₂} {W : ClosedVal A₂}
                    {M₁ : Γ , A₁ ⊢c C} {M₂ : Γ , A₂ ⊢c C} {T : ClosedTerminal C}
    → γ ⊢v V ⇓ `inj₂ W
    → (γ ++ W) ⊢c M₂ ⇓ T
      ---------------------
    → γ ⊢c case⊎ V M₁ M₂ ⇓ T
