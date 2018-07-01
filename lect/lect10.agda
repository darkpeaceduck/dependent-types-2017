{-# OPTIONS --without-K #-}

module lect10 where

open import Data.Sum
open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Nat
open import Data.Unit
open import Function

open import Trunc

-- 1. Пропозициональное обрезание.

data Tr (A : Set) : Set where
  tr : A → Tr A

-- ∥_∥ : Set → Set
-- ∣_∣ : {A : Set} → A → ∥ A ∥
-- trunc : {A : Set} → isProp (∥ A ∥)
-- Trunc-rec : {A B : Set} → isProp B → (A → B) → ∥ A ∥ → B

_∨_ : Set → Set → Set
A ∨ B = ∥ A ⊎ B ∥

∨-isProp : (A B : Set) → isProp (A ∨ B)
∨-isProp A B = trunc

inl : {A B : Set} → A → A ∨ B
inl a = ∣ inj₁ a ∣

inr : {A B : Set} → B → A ∨ B
inr b = ∣ inj₂ b ∣

∨-elim : {A B C : Set} → isProp C → (A → C) → (B → C) → A ∨ B → C
∨-elim {A} {B} {C} p f g = Trunc-rec p lem
  where
    lem : A ⊎ B → C
    lem (inj₁ a) = f a
    lem (inj₂ b) = g b
-- ∨-elim p f g (∣ inj₁ a ∣) = f a
-- ∨-elim p f g (∣ inj₂ b ∣) = g b

∃ : (A : Set) (B : A → Set) → Set
∃ A B = ∥ Σ A B ∥

Σ' = Σ

syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

∃-isProp : (A : Set) (B : A → Set) → isProp (∃ A B)
∃-isProp A B = trunc

-- Упражнение
∃-intro : {A : Set} {B : A → Set} → (a : A) → B a → ∃[ x ∶ A ] (B x)
∃-intro = {!!}

∃-elim : {A : Set} {B : A → Set} {C : Set} → isProp C → ((a : A) → B a → C) → ∃[ x ∶ A ] (B x) → C
∃-elim = {!!}

-- 2. Предикат "множество не пусто".

inh : Set → Set
inh A = ∃[ x ∶ A ] ⊤

inh' : Set → Set
inh' A = ∥ A ∥
Tr-fun : {A B : Set} (f : A → B) → ∥ A ∥ → ∥ B ∥
Tr-fun f = Trunc-rec trunc (∣_∣ ∘ f)
-- Tr-fun f (∣ a ∣) = ∣ f a ∣

inh-inh' : {A : Set} → inh A → inh' A
inh-inh' = Tr-fun proj₁

inh'-inh : {A : Set} → inh' A → inh A
inh'-inh = Tr-fun (λ a → a , tt)


-- 3. Сюръективные функции.

isInj : {A B : Set} → (A → B) → Set
isInj {A} {B} f = (x x' : A) → f x ≡ f x' → x ≡ x'

isSur : {A B : Set} → (A → B) → Set
isSur {A} {B} f = (b : B) → ∃[ a ∶ A ] (f a ≡ b)

sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'}
  (p : a ≡ a') →
  subst B p b ≡ b' →
  _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl refl = refl

-- { x ∈ A | B } → A

emb-isInj : {A : Set} {B : A → Set} → ((x : A) → isProp (B x))
            → isInj {Σ A B} proj₁
emb-isInj {A} {B} pB (a , b) (.a , b') refl = sigmaExt {A} {B} {a} {a} {b} {b'} refl (pB a b b')

factor-lem : {A B : Set} (f : A → B) →
  Σ[ C ∶ Set ]
  Σ[ g ∶ (A → C) ]
  Σ[ h ∶ (C → B) ]
  (isSur g × isInj h × (h ∘ g ≡ f))
factor-lem {A} {B} f = (Σ[ b ∶ B ] ∃[ a ∶ A ] (f a ≡ b)) , (λ a → f a , ∣ a , refl ∣) , proj₁ , (λ t → Tr-fun (λ s → proj₁ s , sigmaExt (proj₂ s) (trunc _ _)) (proj₂ t)) , (emb-isInj (λ x → trunc)) , refl

-- 4. Фактор множества через HIT.

-- 5. Фактор множества.

record EqRel (A : Set) : Set₁ where
  constructor eqrel
  field
    R : A → A → Set
    R-isProp : (x y : A) → isProp (R x y)
    R-refl : (x : A) → R x x
    R-sym : (x y : A) → R x y → R y x
    R-trans : (x y z : A) → R x y → R y z → R x z

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

_/_ : (A : Set) → EqRel A → Set₁
A / e = let open EqRel e in
  Σ[ P ∶ (A → hProp) ]
  ((∃[ x ∶ A ] (hProp.A (P x))) ×
  ((x y : A) → hProp.A (P x) → R x y ↔ hProp.A (P y)))

[_] : {A : Set} {e : EqRel A} → A → A / e
[_] {A} {e} a = (λ a' → prop (EqRel.R e a a') (EqRel.R-isProp e a a')) ,
  ∣ a , EqRel.R-refl e a ∣ , {!!}
