open import CBPV.Syntax renaming ( _,_ to _,,_ )
open import CBPV.BigStep

open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

module CBPV.LogicalRelation where

empty : Env ∅
empty = λ ()

⇓v-well-defined : ∅ ⊢v A → Set
⇓v-well-defined V = ∃[ W ] empty ⊢v V ⇓ W

⇓c-well-defined : ∅ ⊢c C → Set
⇓c-well-defined M = ∃[ T ] empty ⊢c M ⇓ T

mutual
  𝓥⟦_⟧ : ∀ (A : ValType) → ClosedVal A → Set
  𝓥⟦ `⊤ ⟧ `tt = ⊤
  𝓥⟦ 𝑼 C ⟧ [｛ M ｝⨾ γ ] = 𝓜⟦ C ⟧ M γ
  𝓥⟦ A₁ `× A₂ ⟧ `⟨ W₁ , W₂ ⟩ = 𝓥⟦ A₁ ⟧ W₁ × 𝓥⟦ A₂ ⟧ W₂
  𝓥⟦ A₁ `⊎ A₂ ⟧ (`inj₁ W) = 𝓥⟦ A₁ ⟧ W
  𝓥⟦ A₁ `⊎ A₂ ⟧ (`inj₂ W) = 𝓥⟦ A₂ ⟧ W

  𝓒⟦_⟧ : ∀ (C : CompType) → ClosedTerminal C → Set
  𝓒⟦ A ⇒ C ⟧ [ƛ M ⨾ γ ] = ∀ (W : ClosedVal A) → 𝓥⟦ A ⟧ W → 𝓜⟦ C ⟧ M (γ ++ W)
  𝓒⟦ 𝑭 A ⟧ (return W) = 𝓥⟦ A ⟧ W
  𝓒⟦ C₁ & C₂ ⟧ [ƛ⟨ M₁ , M₂ ⟩⨾ γ ] = 𝓜⟦ C₁ ⟧ M₁ γ × 𝓜⟦ C₂ ⟧ M₂ γ
  
  𝓜⟦_⟧ : ∀ (C : CompType) → Γ ⊢c C → Env Γ → Set
  𝓜⟦ C ⟧ M γ = ∃[ T ] γ ⊢c M ⇓ T × 𝓒⟦ C ⟧ T

_⊨_ : ∀ (Γ : Context) → Env Γ → Set
Γ ⊨ γ = ∀ {A : ValType} → (x : Γ ∋ A) → 𝓥⟦ A ⟧ (γ x)

infix 4 _⊨_

_^_ : ∀ {γ : Env Γ} {W : ClosedVal A}
  → Γ ⊨ γ → 𝓥⟦ A ⟧ W → Γ ,, A ⊨ γ ++ W
(Γ⊨γ ^ W) Z = W
(Γ⊨γ ^ W) (S x) = Γ⊨γ x

infixl 5 _^_

val-semantic-typing : Γ ⊢v A → Set
val-semantic-typing {Γ} {A} V =
  ∀ {γ : Env Γ} → Γ ⊨ γ → ∃[ W ] γ ⊢v V ⇓ W × 𝓥⟦ A ⟧ W

comp-semantic-typing : Γ ⊢c C → Set
comp-semantic-typing {Γ} {C} M =
  ∀ {γ : Env Γ} → Γ ⊨ γ → 𝓜⟦ C ⟧ M γ

syntax val-semantic-typing {Γ} {A} V = Γ ⊨v V ∷ A
syntax comp-semantic-typing {Γ} {C} M = Γ ⊨c M ∷ C

mutual
  val-fundamental : ∀ (V : Γ ⊢v A) → Γ ⊨v V ∷ A
  val-fundamental (` x) {γ} Γ⊨γ = γ x , ⇓v-var refl , Γ⊨γ x
  val-fundamental `tt Γ⊨γ = `tt , ⇓v-tt , tt
  val-fundamental ｛ M ｝ {γ} Γ⊨γ with comp-fundamental M Γ⊨γ
  ... | T , M⇓ , 𝓒T = [｛ M ｝⨾ γ ] , ⇓v-thunk , T , M⇓ , 𝓒T
  val-fundamental `⟨ V₁ , V₂ ⟩ Γ⊨γ with val-fundamental V₁ Γ⊨γ | val-fundamental V₂ Γ⊨γ
  ... | W₁ , V₁⇓ , 𝓥W₁ | W₂ , V₂⇓ , 𝓥W₂ = `⟨ W₁ , W₂ ⟩ , ⇓v-pair V₁⇓ V₂⇓ , 𝓥W₁ , 𝓥W₂
  val-fundamental (`inj₁ V) Γ⊨γ with val-fundamental V Γ⊨γ
  ... | W , V⇓ , 𝓥W = `inj₁ W , ⇓v-inj₁ V⇓ , 𝓥W
  val-fundamental (`inj₂ V) Γ⊨γ with val-fundamental V Γ⊨γ
  ... | W , V⇓ , 𝓥W = `inj₂ W , ⇓v-inj₂ V⇓ , 𝓥W

  comp-fundamental : ∀ (M : Γ ⊢c C) → Γ ⊨c M ∷ C
  comp-fundamental (ƛ M) {γ} Γ⊨γ =
    [ƛ M ⨾ γ ] , ⇓c-abs , λ W 𝓥W → comp-fundamental M (Γ⊨γ ^ 𝓥W)
  comp-fundamental (M · V) Γ⊨γ
      with comp-fundamental M Γ⊨γ
  ... | [ƛ L ⨾ δ ] , M⇓ , 𝓒Lδ
      with val-fundamental V Γ⊨γ
  ... | W , V⇓ , 𝓥W =
    let
      T , L⇓ , 𝓒T = 𝓒Lδ W 𝓥W
    in T , ⇓c-app M⇓ V⇓ L⇓ , 𝓒T
  comp-fundamental (V !) Γ⊨γ  with val-fundamental V Γ⊨γ
  ... | [｛ M ｝⨾ δ ] , V⇓ , T , M⇓ , 𝓒T = T , ⇓c-force V⇓ M⇓ , 𝓒T
  comp-fundamental (V ⨾ M) Γ⊨γ with val-fundamental V Γ⊨γ | comp-fundamental M Γ⊨γ
  ... | `tt , V⇓ , tt | T , M⇓ , 𝓒T = T , ⇓c-seq V⇓ M⇓ , 𝓒T
  comp-fundamental ƛ⟨ M₁ , M₂ ⟩ {γ} Γ⊨γ =
    [ƛ⟨ M₁ , M₂ ⟩⨾ γ ] , ⇓c-pair , comp-fundamental M₁ Γ⊨γ , comp-fundamental M₂ Γ⊨γ
  comp-fundamental (`proj₁ M) Γ⊨γ with comp-fundamental M Γ⊨γ
  ... | [ƛ⟨ M₁ , _ ⟩⨾ δ ] , M⇓ , (T , M₁⇓ , 𝓒T) , _ = T , ⇓c-proj₁ M⇓ M₁⇓ , 𝓒T
  comp-fundamental (`proj₂ M) Γ⊨γ with comp-fundamental M Γ⊨γ
  ... | [ƛ⟨ _ , M₂ ⟩⨾ δ ] , M⇓ , _ , (T , M₂⇓ , 𝓒T) = T , ⇓c-proj₂ M⇓ M₂⇓ , 𝓒T
  comp-fundamental (return V) Γ⊨γ  with val-fundamental V Γ⊨γ
  ... | W , V⇓ , 𝓥W = return W , ⇓c-return V⇓ , 𝓥W
  comp-fundamental (`let V M) Γ⊨γ
      with val-fundamental V Γ⊨γ
  ... | W , V⇓ , 𝓥W
      with comp-fundamental M (Γ⊨γ ^ 𝓥W)
  ... | T , M⇓ , 𝓒T = T , ⇓c-let V⇓ M⇓ , 𝓒T
  comp-fundamental (M to N) Γ⊨γ
      with comp-fundamental M Γ⊨γ
  ... | return W , M⇓ , 𝓥W
      with comp-fundamental N (Γ⊨γ ^ 𝓥W)
  ... | T , N⇓ , 𝓒T = T , ⇓c-to M⇓ N⇓ , 𝓒T
  comp-fundamental (case× V M) Γ⊨γ
      with val-fundamental V Γ⊨γ
  ... | `⟨ W₁ , W₂ ⟩ , V⇓ , 𝓥W₁ , 𝓥W₂
      with comp-fundamental M (Γ⊨γ ^ 𝓥W₁ ^ 𝓥W₂)
  ... | T , M⇓ , 𝓒T = T , ⇓c-case× V⇓ M⇓ , 𝓒T
  comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ with val-fundamental V Γ⊨γ
  comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₁ W , V⇓ , 𝓥W with comp-fundamental M₁ (Γ⊨γ ^ 𝓥W)
  comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₁ W , V⇓ , 𝓥W | T , N⇓ , 𝓒T
    = T , ⇓c-case⊎-inj₁ V⇓ N⇓ , 𝓒T
  comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₂ W , V⇓ , 𝓥W with comp-fundamental M₂ (Γ⊨γ ^ 𝓥W)
  comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₂ W , V⇓ , 𝓥W | T , N⇓ , 𝓒T
    = T , ⇓c-case⊎-inj₂ V⇓ N⇓ , 𝓒T

⇓v-total : ∀ (V : ∅ ⊢v A) → ⇓v-well-defined V
⇓v-total V with val-fundamental V {γ = λ ()} (λ ())
... | W , V⇓ , _ = W , V⇓

⇓c-total : ∀ (M : ∅ ⊢c C) → ⇓c-well-defined M
⇓c-total M with comp-fundamental M {γ = λ ()} (λ ())
... | T , M⇓ , _ = T , M⇓
