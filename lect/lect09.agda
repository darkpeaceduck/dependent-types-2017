{-# OPTIONS --without-K #-}

module lect09 where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.Sum

-- 1. Утверждения

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

Bool-is-not-Prop : isProp Bool → ⊥
Bool-is-not-Prop p = subst T (p true false) tt

-- 2. Какие предикаты являются настоящими предикатами (то есть возвращают утверждения)?
--    ⊤, ⊥, ∧, ∨, →, ∀, ∃, ≡, рекурсвиные предикаты, индуктивные предикаты.

-- ⊤
⊤-isProp : isProp ⊤
⊤-isProp _ _ = refl

-- ⊥
⊥-isProp : isProp ⊥
⊥-isProp x ()

_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc n == suc m = n == m

_==''_ : ℕ → ℕ → Set
0 =='' 0 = ⊤
0 =='' suc _ = ⊥
suc _ =='' 0 = ⊥
suc n =='' suc m = n =='' m

==-isProp : (n m : ℕ) → isProp (n =='' m)
==-isProp zero zero = ⊤-isProp
==-isProp zero (suc m) = ⊥-isProp
==-isProp (suc n) zero = ⊥-isProp
==-isProp (suc n) (suc m) = ==-isProp n m

data _<=_ : ℕ → ℕ → Set where
  z<=n : {n : ℕ} → 0 <= n
  s<=s : {n m : ℕ} → n <= m → suc n <= suc m

<=-isProp : {n m : ℕ} → isProp (n <= m)
<=-isProp z<=n z<=n = refl
<=-isProp (s<=s p) (s<=s q) = cong s<=s (<=-isProp p q)

-- Не любой индуктивно определенный тип является предикатом.
data _<='_ : ℕ → ℕ → Set where
  z<='n : {n : ℕ} → 0 <=' n
  foo : {n : ℕ} → n <=' n
  s<='s : {n m : ℕ} → n <=' m → suc n <=' suc m

×-isProp : {A B : Set} → isProp A → isProp B → isProp (A × B)
×-isProp p q t s = cong₂ _,_ (p _ _) (q _ _)

∀-isProp' : {A : Set} (B : A → Set) → ((x : A) → isProp (B x))
            → isProp ((x : A) → B x)
∀-isProp' = {!!}

-- Тип утверждений.
record Prop : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

postulate
  funExt : {A : Set} (B : A → Set) (f g : (x : A) → B x)
           → ((x : A) → f x ≡ g x) → f ≡ g

-- У нас есть квантор всеобщности и конъюнкция.
∀-isProp : {A : Set} {B : A → Prop} → isProp ((x : A) → Prop.A (B x))
∀-isProp {A} {B} f g =
  funExt (λ x → Prop.A (B x)) f g (λ x → Prop.proof (B x) (f x) (g x))



-- Но нет дизъюнкции и квантора существования.
⊎-isProp : ({A B : Set} → isProp A → isProp B → isProp (A ⊎ B)) → ⊥
⊎-isProp P = lem (P ⊤-isProp ⊤-isProp (inj₁ tt) (inj₂ tt))
  where
    lem : inj₁ tt ≡ inj₂ tt → ⊥
    lem ()

-- Это неверно
-- ∃-isProp : {A : Set} {B : A → Prop} → isProp (Σ A (λ x → Prop.A (B x)))
-- ∃-isProp = {!!}

-- data _≡'_ {A : Set} (x : A) : A → Set where
--   refl : x ≡' x

J : (A : Set) (x : A) → (C : (y : A) → x ≡ y → Set) → C x refl
    → (y : A) (p : x ≡ y) → C y p
J A x C c .x refl = c

-- data _≡'_ {A : Set} : A → A → Set where
--   refl : (x : A) → x ≡' x

J' : (A : Set) → (C : (x y : A) → x ≡ y → Set) → ((x : A) → C x x refl)
    → (x y : A) (p : x ≡ y) → C x y p
J' A C c x .x refl = c x

K : {A : Set} (x : A) (C : x ≡ x → Set) → C refl → (p : x ≡ x) → C p
K x C c p = {!!}

-- У нас нет равнеств
≡-isProp : {A : Set} (x y : A) → isProp (x ≡ y)
≡-isProp x .x refl q = {!!}

-- 3. Множества

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

⊥-isSet : isSet ⊥
⊥-isSet () y p q

data Unit : Set where
  unit : Unit

Unit-isSet : isSet Unit
Unit-isSet = {!!} -- x .x refl refl = refl

-- Пока без доказательства
isSet-lem : {A : Set} (R : A → A → Prop) →
  ((x y : A) → x ≡ y → Prop.A (R x y)) →
  ((x y : A) → Prop.A (R x y) → x ≡ y) →
  isSet A
isSet-lem R f g = {!!}

==-≡ : (x y : ℕ) → x =='' y → x ≡ y
==-≡ zero zero p = refl
==-≡ zero (suc y) ()
==-≡ (suc x) zero ()
==-≡ (suc x) (suc y) p = cong suc (==-≡ x y p)

≡-== : (x y : ℕ) → x ≡ y → x =='' y
≡-== zero zero p = tt
≡-== zero (suc y) ()
≡-== (suc x) zero ()
≡-== (suc x) (suc y) p = ≡-== x y (cong pred p)

ℕ-isSet : isSet ℕ
ℕ-isSet = isSet-lem (λ x y → prop (x =='' y) (==-isProp x y)) ≡-== ==-≡

Unit-isSet' : isSet Unit
Unit-isSet' = isSet-lem (λ x y → prop ⊤ ⊤-isProp) (λ x y p → tt) (λ x y _ → lem x y)
  where
    lem : (x y : Unit) → x ≡ y
    lem unit unit = refl

==L : {A : Set} (p : isSet A) → List A → List A → Prop
==L _ [] [] = prop ⊤ ⊤-isProp
==L _ [] (x ∷ ys) = prop ⊥ ⊥-isProp
==L _ (x ∷ xs) [] = prop ⊥ ⊥-isProp
==L p (x ∷ xs) (y ∷ ys) = prop (x ≡ y × Prop.A (==L p xs ys)) (×-isProp (p x y) (Prop.proof (==L p xs ys)))

==L-≡ : {A : Set} (p : isSet A) (xs ys : List A) → Prop.A (==L p xs ys) → xs ≡ ys
==L-≡ p [] [] q = refl
==L-≡ p [] (x ∷ ys) ()
==L-≡ p (x ∷ xs) [] ()
==L-≡ p (x ∷ xs) (x₁ ∷ ys) q = cong₂ _∷_ (proj₁ q) (==L-≡ p xs ys (proj₂ q))

≡-==L : {A : Set} (p : isSet A) (xs ys : List A) → xs ≡ ys → Prop.A (==L p xs ys)
≡-==L p [] [] q = tt
≡-==L p [] (x ∷ ys) ()
≡-==L p (x ∷ xs) [] ()
≡-==L p (x ∷ xs) (y ∷ ys) q = cong (headDef x) q , ≡-==L p xs ys (cong tail q)
  where
    headDef : {A : Set} → A → List A → A
    headDef a [] = a
    headDef _ (x ∷ xs) = x

    tail : {A : Set} → List A → List A
    tail [] = []
    tail (x ∷ xs) = xs

List-isSet : {A : Set} → isSet A → isSet (List A)
List-isSet p = isSet-lem (==L p) (≡-==L p) (==L-≡ p)
