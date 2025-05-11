open import Relation.Binary.PropositionalEquality

open import Eff.Syntax
open import Eff.Thinnings

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
        --------------------
      → ClosedVal (A₁ `⊎ A₂)
    
    `inj₂ :
        ClosedVal A₂
        --------------------
      → ClosedVal (A₁ `⊎ A₂)
    
    `⟨_,_⟩ :
        ClosedVal A₁
      → ClosedVal A₂
        --------------------
      → ClosedVal (A₁ `× A₂)
    
    [｛_｝⨾_] :
        Γ ⊢⟨ E ⟩c C
      → Env Γ
        --------------------
      → ClosedVal (𝑼⟨ E ⟩ C)

_⊕⊕_ : Env Γ → Env Δ → Env (Γ ++ Δ)
_⊕⊕_ {Δ = ∅}     γ δ x     = γ x
_⊕⊕_ {Δ = Δ , A} γ δ Z     = δ Z
_⊕⊕_ {Δ = Δ , A} γ δ (S x) = (γ ⊕⊕ λ z → δ (S z)) x

_,,_ : Env Γ → ClosedVal A → Env (Γ , A)
(γ ,, a) Z     = a
(γ ,, a) (S x) = γ x

infixl 6 _,,_

data ClosedTerminal : Effect → CompType → Set where

  return_ :
      ClosedVal A
      --------------------
    → ClosedTerminal E (𝑭 A)

  [op[_]_⟨ƛ_⟩⨾_] :
      A ↝ B ∈ E
    → ClosedVal A
    → Γ , B ⊢⟨ E ⟩c C
    → Env Γ
      ------------------
    → ClosedTerminal E C

  [ƛ_⨾_] :
      Γ , A ⊢⟨ E ⟩c C
    → Env Γ
      ------------------------
    → ClosedTerminal E (A ⇒ C)
  
  [ƛ⟨_,_⟩⨾_] :
      Γ ⊢⟨ E ⟩c C₁
    → Γ ⊢⟨ E ⟩c C₂
    → Env Γ
      --------------------------
    → ClosedTerminal E (C₁ & C₂)

infix 6 return_

data _⊢v_⇓_ : Env Γ → Γ ⊢v A → ClosedVal A → Set where

  ⇓v-var : ∀ {γ : Env Γ} {x : Γ ∋ A} {W : ClosedVal A}
    → γ x ≡ W
      ------------
    → γ ⊢v ` x ⇓ W
    
  ⇓v-tt : ∀ {γ : Env Γ}
      --------------
    → γ ⊢v `tt ⇓ `tt

  ⇓v-thunk : ∀ {γ : Env Γ} {M : Γ ⊢⟨ E ⟩c C}
    → γ ⊢v ｛ M ｝ ⇓ [｛ M ｝⨾ γ ]

  ⇓v-pair : ∀ {γ : Env Γ}
              {V₁ : Γ ⊢v A₁} {W₁ : ClosedVal A₁}
              {V₂ : Γ ⊢v A₂} {W₂ : ClosedVal A₂}
    → γ ⊢v V₁ ⇓ W₁
    → γ ⊢v V₂ ⇓ W₂
      --------------------------------
    → γ ⊢v `⟨ V₁ , V₂ ⟩ ⇓ `⟨ W₁ , W₂ ⟩

  ⇓v-inj₁ : ∀ {A₂ : ValType} {γ : Env Γ} {V : Γ ⊢v A₁} {W : ClosedVal A₁}
    → γ ⊢v V ⇓ W
      --------------------------------
    → γ ⊢v `inj₁ {A₂ = A₂} V ⇓ `inj₁ W

  ⇓v-inj₂ : ∀ {A₁ : ValType} {γ : Env Γ} {V : Γ ⊢v A₂} {W : ClosedVal A₂}
    → γ ⊢v V ⇓ W
      --------------------------------
    → γ ⊢v `inj₂ {A₁ = A₁} V ⇓ `inj₂ W

data _⊢⟨_⟩c_⇓_ : Env Γ → (E : Effect) → Γ ⊢⟨ E ⟩c C → ClosedTerminal E C → Set where

  ⇓c-op : ∀ {γ : Env Γ}
            {M : Γ , B ⊢⟨ E ⟩c C}
            {V : Γ ⊢v A} {W : ClosedVal A}
    → (i : A ↝ B ∈ E)
    → γ ⊢v V ⇓ W
      -------------------------------------------------
    → γ ⊢⟨ E ⟩c op[ i ] V ⟨ƛ M ⟩ ⇓ [op[ i ] W ⟨ƛ M ⟩⨾ γ ]

  ⇓c-handle-return : ∀ {γ : Env Γ}
                       {M : Γ ⊢⟨ E ⟩c 𝑭 A} {W : ClosedVal A}
                       {H : Γ ⊢h A [ E ]⇛[ F ] C}
                       {T : ClosedTerminal F C}
    → γ ⊢⟨ E ⟩c M ⇓ (return W)
    → (γ ,, W) ⊢⟨ F ⟩c return-clause H ⇓ T
      ------------------------------------
    → γ ⊢⟨ F ⟩c `with H handle M ⇓ T

  ⇓c-handle-op : ∀ {γ : Env Γ} {δ : Env Δ}
                   {A′ B′ : ValType} {i : A′ ↝ B′ ∈ E}
                   {M : Γ ⊢⟨ E ⟩c 𝑭 A} {N : Δ , B′ ⊢⟨ E ⟩c 𝑭 A}
                   {W : ClosedVal A′}
                   {H : Γ ⊢h A [ E ]⇛[ F ] C}
                   {T : ClosedTerminal F C}
    → γ ⊢⟨ E ⟩c M ⇓ [op[ i ] W ⟨ƛ N ⟩⨾ δ ]
    → (γ ,, W ,, [｛ ƛ `with (H ↑h wkᵣ) handle (N ↑c wkₗ) ｝⨾ γ ⊕⊕ δ ]) ⊢⟨ F ⟩c op-clause i H ⇓ T
      ------------------------------
    → γ ⊢⟨ F ⟩c `with H handle M ⇓ T

  ⇓c-abs : ∀ {γ : Env Γ} {M : Γ , A ⊢⟨ E ⟩c C}
      --------------------------
    → γ ⊢⟨ E ⟩c ƛ M ⇓ [ƛ M ⨾ γ ]

  ⇓c-app-elim : ∀ {γ : Env Γ} {δ : Env Δ}
                  {M : Γ ⊢⟨ E ⟩c A ⇒ C} {N : Δ , A ⊢⟨ E ⟩c C}
                  {V : Γ ⊢v A} {W : ClosedVal A}
                  {T : ClosedTerminal E C}
    → γ ⊢⟨ E ⟩c M ⇓ [ƛ N ⨾ δ ]
    → γ ⊢v V ⇓ W
    → (δ ,, W) ⊢⟨ E ⟩c N ⇓ T
      -------------------
    → γ ⊢⟨ E ⟩c M · V ⇓ T

  ⇓c-app-op : ∀ {γ : Env Γ} {δ : Env Δ}
                {A′ B′ : ValType} {i : A′ ↝ B′ ∈ E}
                {M : Γ ⊢⟨ E ⟩c A ⇒ C}
                {N : Δ , B′ ⊢⟨ E ⟩c A ⇒ C} {W : ClosedVal A′}
                {V : Γ ⊢v A}
    → γ ⊢⟨ E ⟩c M ⇓ [op[ i ] W ⟨ƛ N ⟩⨾ δ ]
      -------------------
    → γ ⊢⟨ E ⟩c M · V ⇓ [op[ i ] W ⟨ƛ (N ↑c wkₗ) · (V ↑v wkᵣ) ⟩⨾ γ ⊕⊕ δ ]

  ⇓c-force : ∀ {γ : Env Γ} {δ : Env Δ}
               {V : Γ ⊢v 𝑼⟨ E ⟩ C} {M : Δ ⊢⟨ E ⟩c C}
               {T : ClosedTerminal E C}
    → γ ⊢v V ⇓ [｛ M ｝⨾ δ ]
    → δ ⊢⟨ E ⟩c M ⇓ T
      ---------------------
    → γ ⊢⟨ E ⟩c V ! ⇓ T

  ⇓c-seq : ∀ {γ : Env Γ}
             {V : Γ ⊢v `⊤}
             {M : Γ ⊢⟨ E ⟩c C} {T : ClosedTerminal E C}
    → γ ⊢v V ⇓ `tt
    → γ ⊢⟨ E ⟩c M ⇓ T
      -------------------
    → γ ⊢⟨ E ⟩c V ⨾ M ⇓ T

  ⇓c-pair : ∀ {γ : Env Γ}
              {M₁ : Γ ⊢⟨ E ⟩c C₁} {M₂ : Γ ⊢⟨ E ⟩c C₂}
      -------------------------------------------
    → γ ⊢⟨ E ⟩c ƛ⟨ M₁ , M₂ ⟩ ⇓ [ƛ⟨ M₁ , M₂ ⟩⨾ γ ]

  ⇓c-proj₁-elim : ∀ {γ : Env Γ} {δ : Env Δ}
                    {M : Γ ⊢⟨ E ⟩c C₁ & C₂} {M₁ : Δ ⊢⟨ E ⟩c C₁} {M₂ : Δ ⊢⟨ E ⟩c C₂}
                    {T : ClosedTerminal E C₁}
    → γ ⊢⟨ E ⟩c M ⇓ [ƛ⟨ M₁ , M₂ ⟩⨾ δ ]
    → δ ⊢⟨ E ⟩c M₁ ⇓ T
      --------------------------------
    → γ ⊢⟨ E ⟩c `proj₁ M ⇓ T

  ⇓c-proj₁-op : ∀ {γ : Env Γ} {δ : Env Δ}
                  {A′ B′ : ValType} {i : A′ ↝ B′ ∈ E}
                  {M : Γ ⊢⟨ E ⟩c C₁ & C₂}
                  {N : Δ , B′ ⊢⟨ E ⟩c C₁ & C₂} {W : ClosedVal A′}
    → γ ⊢⟨ E ⟩c M ⇓ [op[ i ] W ⟨ƛ N ⟩⨾ δ ]
      --------------------------------
    → γ ⊢⟨ E ⟩c `proj₁ M ⇓ [op[ i ] W ⟨ƛ `proj₁ N ⟩⨾ δ ]

  ⇓c-proj₂-elim : ∀ {γ : Env Γ} {δ : Env Δ}
                    {M : Γ ⊢⟨ E ⟩c C₁ & C₂} {M₁ : Δ ⊢⟨ E ⟩c C₁} {M₂ : Δ ⊢⟨ E ⟩c C₂}
                    {T : ClosedTerminal E C₂}
    → γ ⊢⟨ E ⟩c M ⇓ [ƛ⟨ M₁ , M₂ ⟩⨾ δ ]
    → δ ⊢⟨ E ⟩c M₂ ⇓ T
      --------------------------------
    → γ ⊢⟨ E ⟩c `proj₂ M ⇓ T

  ⇓c-proj₂-op : ∀ {γ : Env Γ} {δ : Env Δ}
                  {A′ B′ : ValType} {i : A′ ↝ B′ ∈ E}
                  {M : Γ ⊢⟨ E ⟩c C₁ & C₂}
                  {N : Δ , B′ ⊢⟨ E ⟩c C₁ & C₂} {W : ClosedVal A′}
    → γ ⊢⟨ E ⟩c M ⇓ [op[ i ] W ⟨ƛ N ⟩⨾ δ ]
      --------------------------------
    → γ ⊢⟨ E ⟩c `proj₂ M ⇓ [op[ i ] W ⟨ƛ `proj₂ N ⟩⨾ δ ]

  ⇓c-return : ∀ {γ : Env Γ}
                {V : Γ ⊢v A} {W : ClosedVal A}
    → γ ⊢v V ⇓ W
      ---------------------------------
    → γ ⊢⟨ E ⟩c (return V) ⇓ (return W)

  ⇓c-let : ∀ {γ : Env Γ}
             {V : Γ ⊢v A} {W : ClosedVal A}
             {M : Γ , A ⊢⟨ E ⟩c C} {T : ClosedTerminal E C}
    → γ ⊢v V ⇓ W
    → (γ ,, W) ⊢⟨ E ⟩c M ⇓ T
      -----------------
    → γ ⊢⟨ E ⟩c `let V M ⇓ T

  ⇓c-to-elim : ∀ {γ : Env Γ}
                 {M : Γ ⊢⟨ E ⟩c 𝑭 A} {W : ClosedVal A}
                 {N : Γ , A ⊢⟨ E ⟩c C} {T : ClosedTerminal E C}
    → γ ⊢⟨ E ⟩c M ⇓ (return W)
    → (γ ,, W) ⊢⟨ E ⟩c N ⇓ T
      ----------------------
    → γ ⊢⟨ E ⟩c M to N ⇓ T

  ⇓c-to-op : ∀ {γ : Env Γ} {δ : Env Δ}
               {A′ B′ : ValType} {i : A′ ↝ B′ ∈ E}
               {M : Γ ⊢⟨ E ⟩c 𝑭 A} {L : Δ , B′ ⊢⟨ E ⟩c 𝑭 A} {W : ClosedVal A′}
               {N : Γ , A ⊢⟨ E ⟩c C}
    → γ ⊢⟨ E ⟩c M ⇓ [op[ i ] W ⟨ƛ L ⟩⨾ δ ]
      ----------------------
    → γ ⊢⟨ E ⟩c M to N ⇓ [op[ i ] W ⟨ƛ (L ↑c wkₗ) to (N ↑c wkᵣ,) ⟩⨾ γ ⊕⊕ δ ]

  ⇓c-case× : ∀ {γ : Env Γ}
               {V : Γ ⊢v A₁ `× A₂} {W₁ : ClosedVal A₁} {W₂ : ClosedVal A₂}
               {M : Γ , A₁ , A₂ ⊢⟨ E ⟩c C } {T : ClosedTerminal E C}
    → γ ⊢v V ⇓ `⟨ W₁ , W₂ ⟩
    → (γ ,, W₁ ,, W₂) ⊢⟨ E ⟩c M ⇓ T
      -----------------------------
    → γ ⊢⟨ E ⟩c case× V M ⇓ T

  ⇓c-case⊎-inj₁ : ∀ {γ : Env Γ}
                    {V : Γ ⊢v A₁ `⊎ A₂} {W : ClosedVal A₁}
                    {M₁ : Γ , A₁ ⊢⟨ E ⟩c C} {M₂ : Γ , A₂ ⊢⟨ E ⟩c C} {T : ClosedTerminal E C}
    → γ ⊢v V ⇓ `inj₁ W
    → (γ ,, W) ⊢⟨ E ⟩c M₁ ⇓ T
      ---------------------------
    → γ ⊢⟨ E ⟩c case⊎ V M₁ M₂ ⇓ T

  ⇓c-case⊎-inj₂ : ∀ {γ : Env Γ}
                    {V : Γ ⊢v A₁ `⊎ A₂} {W : ClosedVal A₂}
                    {M₁ : Γ , A₁ ⊢⟨ E ⟩c C} {M₂ : Γ , A₂ ⊢⟨ E ⟩c C} {T : ClosedTerminal E C}
    → γ ⊢v V ⇓ `inj₂ W
    → (γ ,, W) ⊢⟨ E ⟩c M₂ ⇓ T
      ---------------------------
    → γ ⊢⟨ E ⟩c case⊎ V M₁ M₂ ⇓ T
