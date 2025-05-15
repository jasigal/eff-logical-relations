module Experiment where

open import Level
open import Data.Fin
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Function
open import Function.Bundles using ( _↔_ ; Inverse )
open Inverse
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional using ( Extensionality )

open import Data.Container hiding ( refl )
open import Data.W

-- We need extensionality to prove correctness of the representation
postulate
  ext : Extensionality 0ℓ 0ℓ

-- When we have n operations, we need n indices to reference them
Index : ℕ → Set
Index = Fin

-- An effect is represented by a number of operations and for each operation,
-- an input and output type.
module Effect (E : ℕ) (inp : Index E → Set) (out : Index E → Set) where

  Sᶠ : Set → Set
  Sᶠ X = X ⊎ Σ[ i ∈ Index E ] inp i

  Pᶠ : (X : Set) → Sᶠ X → Set
  Pᶠ _ (inj₁ _)       = ⊥
  Pᶠ _ (inj₂ (i , _)) = out i

  Cᶠ : Set → Container 0ℓ 0ℓ
  Cᶠ X .Shape    = Sᶠ X
  Cᶠ X .Position = Pᶠ X

  -- The container is iso with the effect functor
  Cᶠ-correct : ∀ {X Y : Set} → ⟦ Cᶠ Y ⟧ X ↔ (Y ⊎ Σ[ i ∈ Index E ] inp i × (out i → X))
  Cᶠ-correct .to        = λ { (inj₁ y , f) → inj₁ y ; (inj₂ (i , a) , f) → inj₂ (i , a , f) }
  Cᶠ-correct .from      = λ { (inj₁ y) → (inj₁ y) , λ () ; (inj₂ (i , a , k)) → inj₂ (i , a) , k }
  Cᶠ-correct .to-cong   = λ { refl → refl }
  Cᶠ-correct .from-cong = λ { refl → refl }
  Cᶠ-correct .inverse   =
    (λ { {inj₁ _} refl → refl ; {inj₂ _} refl → refl }) ,
    (λ { {inj₁ y , snd} refl → cong (inj₁ y ,_) (ext λ ()) ; {inj₂ _ , _} refl → refl })

  -- It would be preferable to do this with indexed containers, but that's huge faff.
  -- μ ≡ W, so this is in fact a container as well since containers are closed under W-types.
  Mᶠ : Set → Set
  Mᶠ X = μ (Cᶠ X)

  -- The standard inductive free monad for effects for the above functor
  data M (X : Set) : Set where
    ret : X → M X
    op : (i : Index E) → inp i → (out i → M X) → M X

  -- Our W-type is correct
  Mᶠ-correct : ∀ {X : Set} → Mᶠ X ↔ M X
  Mᶠ-correct = record
    { to = to′
    ; from = from′
    ; to-cong = λ { refl → refl }
    ; from-cong = λ { refl → refl }
    ; inverse = from′-to′ , to′-from′
    }
    where
    to′ : ∀ {X : Set} → Mᶠ X → M X
    to′ (sup (inj₁ x , k)) = ret x
    to′ (sup (inj₂ (i , p) , k)) = op i p (to′ ∘ k)

    from′ : ∀ {X : Set} → M X → Mᶠ X
    from′ (ret x) = sup (inj₁ x , λ ())
    from′ (op i p k) = sup (inj₂ (i , p) , from′ ∘ k)

    from′-to′ : ∀ {X : Set} {x : M X} {y : Mᶠ X} → y ≡ from′ x → to′ y ≡ x
    from′-to′ {x = ret x} refl = refl
    from′-to′ {x = op i p k} refl =
      cong (op i p) (ext (λ z → from′-to′ {x = k z} {y = from′ (k z)} refl))

    to′-from′ : ∀ {X : Set} {x : Mᶠ X} {y : M X} → y ≡ to′ x → from′ y ≡ x
    to′-from′ {x = sup (inj₁ x , k)} refl = cong (λ z → sup (inj₁ x , z)) (ext λ ())
    to′-from′ {x = sup (inj₂ (i , p) , k)} refl =
      cong (λ z → sup (inj₂ (i , p) , z)) (ext (λ z → to′-from′ {x = k z} {y = to′ (k z)} refl))

  -- Handlers
  foldᶠ : ∀ {X Y : Set} → (⟦ Cᶠ X ⟧ Y → Y) → Mᶠ X → Y
  foldᶠ = foldr
