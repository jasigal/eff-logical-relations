open import Eff.Syntax renaming ( _,_ to _,c_ )
open import Eff.BigStep

open import Level
open import Data.Container.Indexed as CI
open import Data.Container as C hiding ( _∈_ )
open import Data.Container.Relation.Unary.All as CAll
open import Data.W as W hiding ( induction )
open import Data.W.Indexed as WI
open import Data.Product
open import Data.Sum
open import Data.Empty.Polymorphic
open import Relation.Unary hiding ( _∈_ )

module Eff.Monad where

module _ (E : Effect) {ℓ : Level}
         (Dom : ValType → Set ℓ)
         (Sub : ∀ (A : ValType) → Pred (Dom A) ℓ)
  where

  Σ-op : Set
  Σ-op = Σ[ (A , B) ∈ (ValType × ValType) ] (A ↝ B ∈ E)

  shp : ValType → Set ℓ
  shp A = Dom A ⊎ Σ[ ((A′ , _) , i) ∈ Σ-op ] Dom A′

  plc : ∀ (A : ValType) → shp A → Set ℓ
  plc _ (inj₁ _)                    = ⊥
  plc _ (inj₂ (((_ , B′) , _) , _)) = Dom B′

  con : ValType → C.Container _ _
  con A .Shape    = shp A
  con A .Position = plc A

  mon : ValType → Set _
  mon A = C.μ (con A)

  pattern ret {abs} x = sup (inj₁ x , abs)
  pattern op {A′} {B′} i p k = sup (inj₂ (((A′ , B′) , i) , p) , k)

  record mon-hypotheses (A : ValType) {P : Pred (mon A) ℓ} : Set ℓ where
    field
      base : ∀ {abs} (x : Dom A) → P (ret {abs} x)
      induct :
        ∀ {A′ B′ : ValType}
        → (i : A′ ↝ B′ ∈ E)
        → (p : Dom A′)
        → (k : Dom B′ → mon A)
        → (∀ (b : Dom B′) → P (k b))
        → P (op i p k)

  open mon-hypotheses

  mon-induction :
    ∀ (A : ValType)
    → (P : Pred (mon A) ℓ)
    → mon-hypotheses A {P}
    → (m : mon A) → P m
  mon-induction A P ih m = W.induction {C = con A} P f m
    where
    f : ∀ {c : C.⟦ con A ⟧ (mon A)} → C.□ (con A) P c → P (sup c)
    f {inj₁ x , _} (all _) = base ih x
    f {inj₂ (((A′ , B′) , i) , p) , k} (all prf) = induct ih i p k prf

  OVER : ∀ (A : ValType) → Set ℓ
  OVER = mon

  COM : ∀ (A : ValType) → Pred (OVER A) ℓ
  COM A (ret x) = Sub A x
  COM A (op {A′ = A′} i p k) = Sub A′ p

  RES : ∀ (A : ValType) → ∀ {o : OVER A} → Pred (COM A o) ℓ
  RES A {ret _} _ = ⊥
  RES A {op {B′ = B′} _ _ _} _ = Σ[ b ∈ Dom B′ ] Sub B′ b

  nxt : ∀ (A : ValType) → ∀ {o : OVER A} → (c : COM A o) → RES A {o} c → OVER A
  nxt A {op _ _ k} _ (b , _) = k b

  CON : ∀ (A : ValType) → CI.Container (OVER A) (OVER A) _ _
  CON A .Command = COM A
  CON A .Response {o} = RES A {o}
  CON A .next {o} = nxt A {o}

  MON : ∀ (A : ValType) → Pred (mon A) _
  MON A = CI.μ (CON A)

  record MON-hypotheses (A : ValType) {P : Pred (mon A) ℓ} : Set ℓ where
    field
      base : ∀ {abs} (x : Dom A) → Sub A x → P (ret {abs} x)
      induct :
        ∀ {A′ B′ : ValType}
        → (i : A′ ↝ B′ ∈ E)
        → (p : Dom A′)
        → (sp : Sub A′ p)
        → (k : Dom B′ → mon A)
        → (∀ (b : Dom B′) → Sub B′ b → P (k b))
        → P (op i p k)

  open MON-hypotheses

  MON-induction : ∀ (A : ValType)
                → ∀ {P : Pred (mon A) ℓ}
                → MON-hypotheses A {P}
                → ∀ {m : mon A} → MON A m → P m
  MON-induction A {P} ih M = iter (CON A) {ℓ = ℓ} {X = P} f M
    where
    f : ∀ {m : mon A} → CI.⟦ CON A ⟧ P m → P m
    f {ret x} (sx , _) = base ih x sx
    f {op i p k} (sp , sk) = induct ih i p sp k λ b sb → sk (b , sb)
