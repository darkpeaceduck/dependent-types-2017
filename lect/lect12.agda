{-# OPTIONS --without-K #-}

module lect12 where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import lect11

lemma'' : {A : Set} (x : A) (p : x ≡ x) → (p ≡ p) ≡ (idp {A} {x} ≡ idp)
lemma'' x p = SetExt ((λ q → trans (sym (inv-left p)) (trans (cong (_**_ (inv p)) q) (inv-left p))) , (λ q → cong (_**_ p) q) , (λ q → {!!}) , {!!})

lemma''' : {A : Set} (x y : A) (p : x ≡ y) → (p ≡ p) ≡ (idp {A} {x} ≡ idp)
lemma''' x .x refl = refl

-- 1. Изоморфизмы алгебраических структур.

record Group : Set₁ where
  field
    A : Set
    set : isSet A
    id : A
    _&_ : A → A → A
    ginv : A → A
    assoc : {x y z : A} → (x & y) & z ≡ x & (y & z)
    id-left : {x : A} → id & x ≡ x
    id-right : {x : A} → x & id ≡ x
    ginv-left : {x : A} → ginv x & x ≡ id
    ginv-right : {x : A} → x & ginv x ≡ id

postulate
  G H : Group

p : G ≡ H -- как доказать равенство двух групп?
p = {!!} -- изоморфизм групп

-- (a , b) : Σ A B
-- (a' , b') : Σ A B
-- (p : a ≡ a') → subst B p b ≡ b' → (a , b) ≡ (a' , b')

record PointedSet : Set₁ where
  field
    A : Set
    id : A
    set : isSet A

-- Σ Set (λ A → A)

-- X, Y : PointedSet
-- p : PointedSet.A X ≡ PointedSet.A Y
-- q : subst (λ A → A) p (Pointed.id X) ≡ Pointed.id Y

subst-lem' : (A B : Set) (p : A ≡ B) (a : A) → subst (λ X → X) p a ≡ ≡-fun p a
subst-lem' A .A refl a = refl

subst-lem : (A B : Set) (p : Bij A B) (a : A) →
  subst (λ X → X) (SetExt p) a ≡ proj₁ p a
subst-lem A B p a = trans (subst-lem' A B (SetExt p) a) {!!}

subst-fun : (A : Set) (B C : A → Set) {a a' : A} (p : a ≡ a')
  (f : B a → C a) →
  subst (λ x → B x → C x) p f ≡ (λ b → subst C p (f (subst B (sym p) b)))
subst-fun A B C refl f = refl

-- Как доказать равенство двух утверждений?

Prop-ext : (A B : Set) → isProp A → isProp B → (A → B) → (B → A)  → A ≡ B
Prop-ext A B Ap Bp f g = SetExt (f , g , (λ x → Ap _ _) , (λ y → Bp _ _))

-- Тип утверждений.

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

hProp-isSet : isSet hProp
hProp-isSet A B = {!!} -- A ≡ B is a proposition since (A ≡ B) ≡ ((A → B) × (B → A)) by SetUnit

-- 2. Любое утверждение является множеством.

isProp-isSet : (A : Set) → isProp A → isSet A
isProp-isSet A t x y p q = trans (r-lem x y p) (sym (r-lem x y q))
  where
    r : (x y : A) → x ≡ y
    r x y = inv (t x x) ** t x y

    r-lem : (x y : A) (s : x ≡ y) → s ≡ r x y
    r-lem x .x refl = inv (inv-left (t x x))

isProp-isProp : (A : Set) → isProp (isProp A)
isProp-isProp A f g = funExt f g (λ x → funExt (f x) (g x) (λ y → isProp-isSet A f x y (f x y) (g x y)))

is-n-Type' : ℕ → Set → Set
is-n-Type' 0 A = isProp A
is-n-Type' (suc n) A = (x y : A) → is-n-Type' n (x ≡ y)

is-n-Type-isProp : (n : ℕ) (A : Set) → isProp (is-n-Type' n A)
is-n-Type-isProp 0 A = isProp-isProp A
is-n-Type-isProp (suc n) A = λ f g → funExt f g (λ x → funExt (f x) (g x) (λ y → is-n-Type-isProp n (x ≡ y) (f x y) (g x y))) 

isSet-isProp : (A : Set) → isProp (isSet A)
isSet-isProp = is-n-Type-isProp 1

isGpd-isProp : (A : Set) → isProp (isGpd A)
isGpd-isProp = is-n-Type-isProp 2

is-n-Type-inc : (n : ℕ) (A : Set) → is-n-Type' n A → is-n-Type' (suc n) A
is-n-Type-inc zero A = isProp-isSet A
is-n-Type-inc (suc n) A = λ t x y → is-n-Type-inc n (x ≡ y) (t x y)

isSet-isGpd : (A : Set) → isSet A → isGpd A
isSet-isGpd = is-n-Type-inc 1

-- 3. isSet-lem.

isSet-lem : {A : Set} (R : A → A → hProp) →
  ({x y : A} → x ≡ y → hProp.A (R x y)) →
  ({x y : A} → hProp.A (R x y) → x ≡ y) →
  isSet A
isSet-lem {A} R f g x y p q = trans (sym (lem₁ p)) (trans (cong g (hProp.proof (R x y) _ _)) (lem₁ q))
  where
    h : {x y : A} → x ≡ y → x ≡ y
    h p = g (f p)

    cancel-right : {A : Set} {x y : A} (p : x ≡ x) (q : x ≡ y) →
                   p ** q ≡ q → p ≡ idp
    cancel-right p refl t = t

    h-idemp : {x y : A} (p : x ≡ y) → h (h p) ≡ h p
    h-idemp {x} {y} p = cong g (hProp.proof (R x y) _ _)

    lem₂ : (h : {x y : A} → x ≡ y → x ≡ y) {x y : A} (p : x ≡ y) →
           h p ≡ h idp ** p
    lem₂ h refl = refl

    lem₁ : {x y : A} (p : x ≡ y) → h p ≡ p
    lem₁ refl = cancel-right (h refl) (h refl) (trans (sym (lem₂ h (h idp))) (h-idemp idp))

-- 4. Pasting diagrams, algebra of oriented simplices.



-- 5. Коммутативность высших групп.

-- 6. HITs.
