open import Eff.Syntax renaming ( _,_ to _,c_ )
open import Eff.BigStep

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded

module Eff.LogicalRelation where

empty : Env ∅
empty = λ ()

⇓v-well-defined : ∅ ⊢v A → Set
⇓v-well-defined V = ∃[ W ] empty ⊢v V ⇓ W

⇓c-well-defined : ∅ ⊢⟨ E ⟩c C → Set
⇓c-well-defined {E = E} M = ∃[ T ] empty ⊢⟨ E ⟩c M ⇓ T

mutual
  𝓥⟦_⟧ : ∀ (A : ValType) → ℕ → ClosedVal A → Set
  𝓥⟦ _ ⟧ zero _ = ⊥
  𝓥⟦ `⊤ ⟧ n@(suc _) `tt = ⊤
  𝓥⟦ 𝑼⟨ E ⟩ C ⟧ n@(suc _) [｛ M ｝⨾ γ ] = 𝓜⟦ C ⟧ n M γ
  𝓥⟦ A₁ `× A₂ ⟧ n@(suc _) `⟨ W₁ , W₂ ⟩ = 𝓥⟦ A₁ ⟧ n W₁ × 𝓥⟦ A₂ ⟧ n W₂
  𝓥⟦ A₁ `⊎ A₂ ⟧ n@(suc _) (`inj₁ W) = 𝓥⟦ A₁ ⟧ n W
  𝓥⟦ A₁ `⊎ A₂ ⟧ n@(suc _) (`inj₂ W) = 𝓥⟦ A₂ ⟧ n W

  𝓒⟦_⟧ : ∀ (C : CompType) → ℕ → ClosedTerminal E C → Set
  𝓒⟦ _ ⟧ zero _ = ⊥
  𝓒⟦ A ⇒ C ⟧ n@(suc _) [ƛ M ⨾ γ ] = ∀ (W : ClosedVal A) → 𝓥⟦ A ⟧ n W → 𝓜⟦ C ⟧ n M (γ ,, W)
  𝓒⟦ A ⇒ C ⟧ (suc n) ([op[_]_⟨ƛ_⟩⨾_] {A = A′} {B = B′} i W N γ) =
    𝓥⟦ A′ ⟧ n W × (∀ (Y : ClosedVal B′) → 𝓥⟦ B′ ⟧ n Y → 𝓜⟦ A ⇒ C ⟧ n N (γ ,, Y))
  𝓒⟦ 𝑭 A ⟧ n@(suc _) (return W) = 𝓥⟦ A ⟧ n W
  𝓒⟦ 𝑭 A ⟧ (suc n) ([op[_]_⟨ƛ_⟩⨾_] {A = A′} {B = B′} i W N γ) =
    𝓥⟦ A′ ⟧ n W × (∀ (Y : ClosedVal B′) → 𝓥⟦ B′ ⟧ n Y → 𝓜⟦ 𝑭 A ⟧ n N (γ ,, Y))
  𝓒⟦ C₁ & C₂ ⟧ n@(suc _) [ƛ⟨ M₁ , M₂ ⟩⨾ γ ] = 𝓜⟦ C₁ ⟧ n M₁ γ × 𝓜⟦ C₂ ⟧ n M₂ γ
  𝓒⟦ C₁ & C₂ ⟧ (suc n) ([op[_]_⟨ƛ_⟩⨾_] {A = A′} {B = B′} i W N γ) =
    𝓥⟦ A′ ⟧ n W × (∀ (Y : ClosedVal B′) → 𝓥⟦ B′ ⟧ n Y → 𝓜⟦ C₁ & C₂ ⟧ n N (γ ,, Y))

  𝓜⟦_⟧ : ∀ (C : CompType) → ℕ → Γ ⊢⟨ E ⟩c C → Env Γ → Set
  𝓜⟦_⟧ C zero _ _ = ⊥
  𝓜⟦_⟧ {E = E} C n@(suc _) M γ = ∃[ T ] γ ⊢⟨ E ⟩c M ⇓ T × (𝓒⟦ C ⟧ n T)

-- mutual
--   𝓥⟦_⟧ : ∀ {T : Type} → (A : ValType) → Acc _⊰_ T → ClosedVal A → Set
--   𝓥⟦ `⊤ ⟧ a `tt = ⊤
--   𝓥⟦ 𝑼⟨ E ⟩ C ⟧ _ [｛ M ｝⨾ γ ] = 𝓜⟦ C ⟧ (⊰-wf (inj₁ E)) M γ
--   𝓥⟦ A₁ `× A₂ ⟧ a `⟨ W₁ , W₂ ⟩ = 𝓥⟦ A₁ ⟧ a W₁ × 𝓥⟦ A₂ ⟧ a W₂
--   𝓥⟦ A₁ `⊎ A₂ ⟧ a (`inj₁ W) = 𝓥⟦ A₁ ⟧ a W
--   𝓥⟦ A₁ `⊎ A₂ ⟧ a (`inj₂ W) = 𝓥⟦ A₂ ⟧ a W

--   𝓒⟦_⟧ : ∀ {T : Type} {p : T ≡ inj₁ E} (C : CompType) → Acc _⊰_ T → ClosedTerminal E C → Set
--   𝓒⟦ A ⇒ C ⟧ a [ƛ M ⨾ γ ] = ∀ (W : ClosedVal A) → 𝓥⟦ A ⟧ a W → 𝓜⟦ C ⟧ a M (γ ,, W)
--   𝓒⟦ 𝑭 A ⟧ a (return W) = 𝓥⟦ A ⟧ a W
--   𝓒⟦ C₁ & C₂ ⟧ a [ƛ⟨ M₁ , M₂ ⟩⨾ γ ] = 𝓜⟦ C₁ ⟧ a M₁ γ × 𝓜⟦ C₂ ⟧ a M₂ γ
--   𝓒⟦_⟧ {E = E} {T = T} {p = p} C a@(acc rs) ([op[_]_⟨ƛ_⟩⨾_] {A = A} {B = B} i W N γ) =
--     let
--       ra = rs {y = inj₂ (inj₁ A)} (subst (λ x → inj₂ (inj₁ A) ⊰ x) (sym p) (⊰-op-inp i))
--       rb = rs {y = inj₂ (inj₁ B)} (subst (λ x → inj₂ (inj₁ B) ⊰ x) (sym p) (⊰-op-out i))
--     in {!!} -- 𝓥⟦ A ⟧ ra W × (∀ (Y : ClosedVal B) → 𝓥⟦ B ⟧ rb Y → 𝓜⟦ C ⟧ a N (γ ,, Y))

--   𝓜⟦_⟧ : ∀ {T : Type} (C : CompType) → Acc _⊰_ T → Γ ⊢⟨ E ⟩c C → Env Γ → Set
--   𝓜⟦_⟧ {E = E} C a M γ = ∃[ T ] γ ⊢⟨ E ⟩c M ⇓ T × (𝓒⟦_⟧ {p = refl} C (⊰-wf (inj₁ E)) T)

-- _⊨_ : ∀ (Γ : Context) → Env Γ → Set
-- Γ ⊨ γ = ∀ {A : ValType} → (x : Γ ∋ A) → 𝓥⟦ A ⟧ (γ x)

-- infix 4 _⊨_

-- _^_ : ∀ {γ : Env Γ} {W : ClosedVal A}
--   → Γ ⊨ γ → 𝓥⟦ A ⟧ W → Γ ,c A ⊨ γ ,, W
-- (Γ⊨γ ^ W) Z = W
-- (Γ⊨γ ^ W) (S x) = Γ⊨γ x

-- infixl 5 _^_

-- val-semantic-typing : Γ ⊢v A → Set
-- val-semantic-typing {Γ} {A} V =
--   ∀ {γ : Env Γ} → Γ ⊨ γ → ∃[ W ] γ ⊢v V ⇓ W × 𝓥⟦ A ⟧ W

-- comp-semantic-typing : Γ ⊢⟨ E ⟩c C → Set
-- comp-semantic-typing {Γ} {E} {C} M =
--   ∀ {γ : Env Γ} → Γ ⊨ γ → 𝓜⟦ C ⟧ M γ

-- syntax val-semantic-typing {Γ} {A} V = Γ ⊨v V ∷ A
-- syntax comp-semantic-typing {Γ} {C} M = Γ ⊨c M ∷ C

-- mutual
--   val-fundamental : ∀ (V : Γ ⊢v A) → Γ ⊨v V ∷ A
--   val-fundamental (` x) {γ} Γ⊨γ = γ x , ⇓v-var refl , Γ⊨γ x
--   val-fundamental `tt Γ⊨γ = `tt , ⇓v-tt , tt
--   val-fundamental ｛ M ｝ {γ} Γ⊨γ with comp-fundamental M Γ⊨γ
--   ... | T , M⇓ , 𝓒T = [｛ M ｝⨾ γ ] , ⇓v-thunk , T , M⇓ , 𝓒T
--   val-fundamental `⟨ V₁ , V₂ ⟩ Γ⊨γ with val-fundamental V₁ Γ⊨γ | val-fundamental V₂ Γ⊨γ
--   ... | W₁ , V₁⇓ , 𝓥W₁ | W₂ , V₂⇓ , 𝓥W₂ = `⟨ W₁ , W₂ ⟩ , ⇓v-pair V₁⇓ V₂⇓ , 𝓥W₁ , 𝓥W₂
--   val-fundamental (`inj₁ V) Γ⊨γ with val-fundamental V Γ⊨γ
--   ... | W , V⇓ , 𝓥W = `inj₁ W , ⇓v-inj₁ V⇓ , 𝓥W
--   val-fundamental (`inj₂ V) Γ⊨γ with val-fundamental V Γ⊨γ
--   ... | W , V⇓ , 𝓥W = `inj₂ W , ⇓v-inj₂ V⇓ , 𝓥W

--   comp-fundamental : ∀ (M : Γ ⊢⟨ E ⟩c C) → Γ ⊨c M ∷ C
--   comp-fundamental (ƛ M) {γ} Γ⊨γ =
--     [ƛ M ⨾ γ ] , ⇓c-abs , λ W 𝓥W → comp-fundamental M (Γ⊨γ ^ 𝓥W)
--   comp-fundamental (M · V) Γ⊨γ
--       with comp-fundamental M Γ⊨γ
--   ... | [ƛ L ⨾ δ ] , M⇓ , 𝓒Lδ
--       with val-fundamental V Γ⊨γ
--   ... | W , V⇓ , 𝓥W =
--     let
--       T , L⇓ , 𝓒T = 𝓒Lδ W 𝓥W
--     in T , ⇓c-app M⇓ V⇓ L⇓ , 𝓒T
--   comp-fundamental (V !) Γ⊨γ  with val-fundamental V Γ⊨γ
--   ... | [｛ M ｝⨾ δ ] , V⇓ , T , M⇓ , 𝓒T = T , ⇓c-force V⇓ M⇓ , 𝓒T
--   comp-fundamental (V ⨾ M) Γ⊨γ with val-fundamental V Γ⊨γ | comp-fundamental M Γ⊨γ
--   ... | `tt , V⇓ , tt | T , M⇓ , 𝓒T = T , ⇓c-seq V⇓ M⇓ , 𝓒T
--   comp-fundamental ƛ⟨ M₁ , M₂ ⟩ {γ} Γ⊨γ =
--     [ƛ⟨ M₁ , M₂ ⟩⨾ γ ] , ⇓c-pair , comp-fundamental M₁ Γ⊨γ , comp-fundamental M₂ Γ⊨γ
--   comp-fundamental (`proj₁ M) Γ⊨γ with comp-fundamental M Γ⊨γ
--   ... | [ƛ⟨ M₁ , _ ⟩⨾ δ ] , M⇓ , (T , M₁⇓ , 𝓒T) , _ = T , ⇓c-proj₁ M⇓ M₁⇓ , 𝓒T
--   comp-fundamental (`proj₂ M) Γ⊨γ with comp-fundamental M Γ⊨γ
--   ... | [ƛ⟨ _ , M₂ ⟩⨾ δ ] , M⇓ , _ , (T , M₂⇓ , 𝓒T) = T , ⇓c-proj₂ M⇓ M₂⇓ , 𝓒T
--   comp-fundamental (return V) Γ⊨γ  with val-fundamental V Γ⊨γ
--   ... | W , V⇓ , 𝓥W = return W , ⇓c-return V⇓ , 𝓥W
--   comp-fundamental (`let V M) Γ⊨γ
--       with val-fundamental V Γ⊨γ
--   ... | W , V⇓ , 𝓥W
--       with comp-fundamental M (Γ⊨γ ^ 𝓥W)
--   ... | T , M⇓ , 𝓒T = T , ⇓c-let V⇓ M⇓ , 𝓒T
--   comp-fundamental (M to N) Γ⊨γ
--       with comp-fundamental M Γ⊨γ
--   ... | return W , M⇓ , 𝓥W
--       with comp-fundamental N (Γ⊨γ ^ 𝓥W)
--   ... | T , N⇓ , 𝓒T = T , ⇓c-to M⇓ N⇓ , 𝓒T
--   comp-fundamental (case× V M) Γ⊨γ
--       with val-fundamental V Γ⊨γ
--   ... | `⟨ W₁ , W₂ ⟩ , V⇓ , 𝓥W₁ , 𝓥W₂
--       with comp-fundamental M (Γ⊨γ ^ 𝓥W₁ ^ 𝓥W₂)
--   ... | T , M⇓ , 𝓒T = T , ⇓c-case× V⇓ M⇓ , 𝓒T
--   comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ with val-fundamental V Γ⊨γ
--   comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₁ W , V⇓ , 𝓥W with comp-fundamental M₁ (Γ⊨γ ^ 𝓥W)
--   comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₁ W , V⇓ , 𝓥W | T , N⇓ , 𝓒T
--     = T , ⇓c-case⊎-inj₁ V⇓ N⇓ , 𝓒T
--   comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₂ W , V⇓ , 𝓥W with comp-fundamental M₂ (Γ⊨γ ^ 𝓥W)
--   comp-fundamental (case⊎ V M₁ M₂) Γ⊨γ | `inj₂ W , V⇓ , 𝓥W | T , N⇓ , 𝓒T
--     = T , ⇓c-case⊎-inj₂ V⇓ N⇓ , 𝓒T

-- ⇓v-total : ∀ (V : ∅ ⊢v A) → ⇓v-well-defined V
-- ⇓v-total V with val-fundamental V {γ = λ ()} (λ ())
-- ... | W , V⇓ , _ = W , V⇓

-- ⇓c-total : ∀ (M : ∅ ⊢c C) → ⇓c-well-defined M
-- ⇓c-total M with comp-fundamental M {γ = λ ()} (λ ())
-- ... | T , M⇓ , _ = T , M⇓
