open import Relation.Binary.PropositionalEquality

open import Eff.Syntax

module Eff.Thinnings where

data _⊑_ : Context → Context → Set where
  nil  :                           ∅     ⊑ ∅
  skip : ∀ {A : ValType} → Γ ⊑ Δ → Γ     ⊑ Δ , A
  keep : ∀ {A : ValType} → Γ ⊑ Δ → Γ , A ⊑ Δ , A

infix 4 _⊑_

idₜ : Γ ⊑ Γ
idₜ {∅} = nil
idₜ {Γ , A} = keep idₜ

_∘ₜ_ : ∀ {Γ Δ Ω} → Δ ⊑ Ω → Γ ⊑ Δ → Γ ⊑ Ω 
nil    ∘ₜ s      = s
skip t ∘ₜ s      = skip (t ∘ₜ s)
keep t ∘ₜ skip s = skip (t ∘ₜ s)
keep t ∘ₜ keep s = keep (t ∘ₜ s)

infixr 5 _∘ₜ_

left-idₜ : ∀ {t : Γ ⊑ Δ} → idₜ ∘ₜ t ≡ t
left-idₜ {t = nil} = refl
left-idₜ {t = skip t} = cong skip left-idₜ
left-idₜ {t = keep t} = cong keep left-idₜ

right-idₜ : ∀ {t : Γ ⊑ Δ} → t ∘ₜ idₜ ≡ t
right-idₜ {t = nil} = refl
right-idₜ {t = skip t} = cong skip right-idₜ
right-idₜ {t = keep t} = cong keep right-idₜ

assoc-∘ₜ : ∀ {Γ Δ Ω Θ : Context} {t : Ω ⊑ Θ} {s : Δ ⊑ Ω} {r : Γ ⊑ Δ}
  → (t ∘ₜ s) ∘ₜ r ≡ t ∘ₜ (s ∘ₜ r)
assoc-∘ₜ {t = nil}                              = refl
assoc-∘ₜ {t = skip t}                           = cong skip (assoc-∘ₜ {t = t})
assoc-∘ₜ {t = keep t} {s = skip s}              = cong skip (assoc-∘ₜ {t = t})
assoc-∘ₜ {t = keep t} {s = keep s} {r = skip r} = cong skip (assoc-∘ₜ {t = t})
assoc-∘ₜ {t = keep t} {s = keep s} {r = keep r} = cong keep (assoc-∘ₜ {t = t})

wkᵣ : Γ ⊑ Γ ++ Δ
wkᵣ {Δ = ∅}     = idₜ
wkᵣ {Δ = Δ , A} = skip wkᵣ

wkₘ : Γ₁ ++ Γ₂ ⊑ (Γ₁ ++ Δ) ++ Γ₂
wkₘ {Γ₂ = ∅} = wkᵣ
wkₘ {Γ₂ = Γ₂ , A} = keep (wkₘ {Γ₂ = Γ₂})

wkᵣ, : Γ , A ⊑ (Γ ++ Δ) , A
wkᵣ, {A = A} = wkₘ {Γ₂ = ∅ , A}

wkₗ : Γ ⊑ Δ ++ Γ
wkₗ {∅}     {∅}     = nil
wkₗ {∅}     {Δ , A} = skip wkₗ
wkₗ {Γ , A} {Δ}     = keep wkₗ

_↑_ : Γ ∋ A → Γ ⊑ Δ → Δ ∋ A
x     ↑ skip t = S (x ↑ t)
Z     ↑ keep t = Z
(S x) ↑ keep t = x ↑ skip t

infixl 5 _↑_

↑-idₜ : ∀ {x : Γ ∋ A} → x ↑ idₜ ≡ x
↑-idₜ {x = Z} = refl
↑-idₜ {x = S x} = cong S_ ↑-idₜ

↑-∘ₜ : ∀ {Γ Δ Ω} {x : Γ ∋ A} {t : Δ ⊑ Ω} {s : Γ ⊑ Δ}
  → x ↑ s ↑ t ≡ x ↑ (t ∘ₜ s)
↑-∘ₜ {x = ()}  {t = nil}    {s = nil}
↑-∘ₜ {x = x}   {t = skip t} {s = s}      = cong S_ (↑-∘ₜ {t = t})
↑-∘ₜ {x = x}   {t = keep t} {s = skip s} = cong S_ (↑-∘ₜ {t = t})
↑-∘ₜ {x = Z}   {t = keep t} {s = keep s} = refl
↑-∘ₜ {x = S x} {t = keep t} {s = keep s} = cong S_ (↑-∘ₜ {t = t})

mutual
  _↑v_ : Γ ⊢v A → Γ ⊑ Δ → Δ ⊢v A
  ` x ↑v t = ` (x ↑ t)
  `tt ↑v t = `tt
  ｛ x ｝ ↑v t = ｛ x ↑c t ｝
  `⟨ V₁ , V₂ ⟩ ↑v t = `⟨ V₁ ↑v t , V₂ ↑v t ⟩
  `inj₁ V ↑v t = `inj₁ (V ↑v t)
  `inj₂ V ↑v t = `inj₂ (V ↑v t)

  _↑c_ : Γ ⊢⟨ E ⟩c C → Γ ⊑ Δ → Δ ⊢⟨ E ⟩c C
  op[ i ] V ⟨ƛ M ⟩ ↑c t = op[ i ] (V ↑v t) ⟨ƛ M ↑c keep t ⟩
  (`with B handle M) ↑c t = `with (B ↑h t) handle (M ↑c t)
  (ƛ M) ↑c t = ƛ (M ↑c keep t)
  M · V ↑c t = (M ↑c t) · (V ↑v t)
  V ! ↑c t = (V ↑v t) !
  V ⨾ M ↑c t = (V ↑v t) ⨾ (M ↑c t)
  ƛ⟨ M₁ , M₂ ⟩ ↑c t = ƛ⟨ M₁ ↑c t , M₂ ↑c t ⟩
  `proj₁ M ↑c t = `proj₁ (M ↑c t)
  `proj₂ M ↑c t = `proj₂ (M ↑c t)
  return V ↑c t = return ( V ↑v t)
  `let V M ↑c t = `let (V ↑v t) (M ↑c keep t)
  (M to N) ↑c t = (M ↑c t) to (N ↑c keep t)
  case× V M ↑c t = case× (V ↑v t) (M ↑c keep (keep t))
  case⊎ V M₁ M₂ ↑c t = case⊎ (V ↑v t) (M₁ ↑c keep t) (M₂ ↑c keep t)

  _↑h_ : Γ ⊢h H → Γ ⊑ Δ → Δ ⊢h H
  return⇒ M ↑h t = return⇒ (M ↑c keep t)
  op⇒ M B ↑h t = op⇒ (M ↑c keep (keep t)) (B ↑h t)

infixl 5 _↑v_
infixl 5 _↑c_
infixl 5 _↑h_

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {u x : A} {v y : B} {w z : C}
  → u ≡ x
  → v ≡ y
  → w ≡ z
    -------------
  → f u v w ≡ f x y z
cong₃ f refl refl refl = refl

mutual
  ↑v-idₜ : ∀ {V : Γ ⊢v A} → V ↑v idₜ ≡ V
  ↑v-idₜ {V = ` x} = cong `_ ↑-idₜ
  ↑v-idₜ {V = `tt} = refl
  ↑v-idₜ {V = ｛ M ｝} = cong ｛_｝ ↑c-idₜ
  ↑v-idₜ {V = `⟨ V₁ , V₂ ⟩} = cong₂ `⟨_,_⟩ ↑v-idₜ ↑v-idₜ
  ↑v-idₜ {V = `inj₁ V} = cong `inj₁ ↑v-idₜ
  ↑v-idₜ {V = `inj₂ V} = cong `inj₂ ↑v-idₜ
  
  ↑c-idₜ : ∀ {M : Γ ⊢⟨ E ⟩c C} → M ↑c idₜ ≡ M
  ↑c-idₜ {M = op[ i ] V ⟨ƛ M ⟩} = cong₂ op[ i ]_⟨ƛ_⟩ ↑v-idₜ ↑c-idₜ
  ↑c-idₜ {M = `with B handle M} = cong₂ `with_handle_ ↑h-idₜ ↑c-idₜ
  ↑c-idₜ {M = ƛ M} = cong ƛ_ ↑c-idₜ
  ↑c-idₜ {M = M · V} = cong₂ _·_ ↑c-idₜ ↑v-idₜ
  ↑c-idₜ {M = V !} = cong _! ↑v-idₜ
  ↑c-idₜ {M = V ⨾ M} = cong₂ _⨾_ ↑v-idₜ ↑c-idₜ
  ↑c-idₜ {M = ƛ⟨ M₁ , M₂ ⟩} = cong₂ ƛ⟨_,_⟩ ↑c-idₜ ↑c-idₜ
  ↑c-idₜ {M = `proj₁ M} = cong `proj₁ ↑c-idₜ
  ↑c-idₜ {M = `proj₂ M} = cong `proj₂ ↑c-idₜ
  ↑c-idₜ {M = return V} = cong return_ ↑v-idₜ
  ↑c-idₜ {M = `let V M} = cong₂ `let ↑v-idₜ ↑c-idₜ
  ↑c-idₜ {M = M to N} = cong₂ _to_ ↑c-idₜ ↑c-idₜ
  ↑c-idₜ {M = case× V M} = cong₂ case× ↑v-idₜ ↑c-idₜ
  ↑c-idₜ {M = case⊎ V M₁ M₂} = cong₃ case⊎ ↑v-idₜ ↑c-idₜ ↑c-idₜ
  
  ↑h-idₜ : ∀ {B : Γ ⊢h H} → B ↑h idₜ ≡ B
  ↑h-idₜ {B = return⇒ M} = cong return⇒ ↑c-idₜ
  ↑h-idₜ {B = op⇒ M B} = cong₂ op⇒ ↑c-idₜ ↑h-idₜ

mutual
  ↑v-∘ₜ : ∀ {Γ Δ Ω} {V : Γ ⊢v A} {t : Δ ⊑ Ω} {s : Γ ⊑ Δ}
    → V ↑v s ↑v t ≡ V ↑v (t ∘ₜ s)
  ↑v-∘ₜ {V = ` x} {t = t} = cong `_ (↑-∘ₜ {t = t})
  ↑v-∘ₜ {V = `tt} = refl
  ↑v-∘ₜ {V = ｛ M ｝} = cong ｛_｝ ↑c-∘ₜ
  ↑v-∘ₜ {V = `⟨ V₁ , V₂ ⟩} = cong₂ `⟨_,_⟩ ↑v-∘ₜ ↑v-∘ₜ
  ↑v-∘ₜ {V = `inj₁ V} = cong `inj₁ ↑v-∘ₜ
  ↑v-∘ₜ {V = `inj₂ V} = cong `inj₂ ↑v-∘ₜ

  ↑c-∘ₜ : ∀ {Γ Δ Ω} {M : Γ ⊢⟨ E ⟩c C} {t : Δ ⊑ Ω} {s : Γ ⊑ Δ}
    → M ↑c s ↑c t ≡ M ↑c (t ∘ₜ s)
  ↑c-∘ₜ {M = op[ i ] V ⟨ƛ M ⟩} = cong₂ op[ i ]_⟨ƛ_⟩ ↑v-∘ₜ ↑c-∘ₜ
  ↑c-∘ₜ {M = `with B handle M} = cong₂ `with_handle_ ↑h-∘ₜ ↑c-∘ₜ
  ↑c-∘ₜ {M = ƛ M} = cong ƛ_ ↑c-∘ₜ
  ↑c-∘ₜ {M = M · V} = cong₂ _·_ ↑c-∘ₜ ↑v-∘ₜ
  ↑c-∘ₜ {M = V !} = cong _! ↑v-∘ₜ
  ↑c-∘ₜ {M = V ⨾ M} = cong₂ _⨾_ ↑v-∘ₜ ↑c-∘ₜ
  ↑c-∘ₜ {M = ƛ⟨ M₁ , M₂ ⟩} = cong₂ ƛ⟨_,_⟩ ↑c-∘ₜ ↑c-∘ₜ
  ↑c-∘ₜ {M = `proj₁ M} = cong `proj₁ ↑c-∘ₜ
  ↑c-∘ₜ {M = `proj₂ M} = cong `proj₂ ↑c-∘ₜ
  ↑c-∘ₜ {M = return V} = cong return_ ↑v-∘ₜ
  ↑c-∘ₜ {M = `let V M} = cong₂ `let ↑v-∘ₜ ↑c-∘ₜ
  ↑c-∘ₜ {M = M to N} = cong₂ _to_ ↑c-∘ₜ ↑c-∘ₜ
  ↑c-∘ₜ {M = case× V M} = cong₂ case× ↑v-∘ₜ ↑c-∘ₜ
  ↑c-∘ₜ {M = case⊎ V M₁ M₂} = cong₃ case⊎ ↑v-∘ₜ ↑c-∘ₜ ↑c-∘ₜ

  ↑h-∘ₜ : ∀ {Γ Δ Ω} {B : Γ ⊢h H} {t : Δ ⊑ Ω} {s : Γ ⊑ Δ}
    → B ↑h s ↑h t ≡ B ↑h (t ∘ₜ s)
  ↑h-∘ₜ {B = return⇒ M} = cong return⇒ ↑c-∘ₜ
  ↑h-∘ₜ {B = op⇒ M B} = cong₂ op⇒ ↑c-∘ₜ ↑h-∘ₜ
