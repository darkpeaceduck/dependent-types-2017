{-# OPTIONS --without-K #-}

module lect11 where

open import Data.Nat
open import Data.Sum
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List
import Level

-- 1. Равенство типов.

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

isBij : ∀ {l k} {A : Set l} {B : Set k} → (A → B) → Set (l Level.⊔ k)
isBij {_} {_} {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

Bij : ∀ {l k} → Set l → Set k → Set (l Level.⊔ k)
Bij A B = Σ[ f ∶ (A → B) ] (isBij f)

isProp : ∀ {l} → Set l → Set l
isProp A = (x y : A) → x ≡ y

isSet : ∀ {l} → Set l → Set l
isSet A = (x y : A) → isProp (x ≡ y)

postulate
  SmallTypesAreSets : (A : Set) → isSet A -- просто, чтобы чуть упростить конструкции.

-- hSet = Σ[ A ∶ Set ] (isSet A)

≡-fun : ∀ {l} {A B : Set l} → A ≡ B → A → B
≡-fun refl x = x

≡-fun-isBij : ∀ {l} {A B : Set l} (p : A ≡ B) → isBij (≡-fun p)
≡-fun-isBij refl = (λ x → x) , ((λ x → refl) , (λ x → refl))

-- theorem : f ≡ g → ((x : A) → f x ≡ g x)
-- axiom   : ((x : A) → f x ≡ g x) → f ≡ g

funExtInv : {A : Set} {B : A → Set} (f g : (x : A) → B x) → f ≡ g → ((x : A) → f x ≡ g x)
funExtInv f .f refl x = refl 

postulate
  funExt : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g

{-
postulate
  SetExt : {A B : Set} → Bij A B → A ≡ B

-- postulate
--   foo : ℕ

Π-isSet : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) → isSet ((x : A) → (B x))
Π-isSet = {!!}

strong-funExt : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) →
  (f g : (x : A) → B x) → (f ≡ g) ≡ ((x : A) → f x ≡ g x)
strong-funExt {A} {B} Bs f g = SetExt (funExtInv f g , funExt f g , (λ p → Π-isSet {A} {B} Bs _ _ _ _) , (λ y → funExt _ _ (λ x → Bs _ _ _ _ _)))
-}

≡-Bij : ∀ {l} {A B : Set l} → A ≡ B → Bij A B
≡-Bij p = ≡-fun p , ≡-fun-isBij p

postulate
  SetUni : ∀ {l} {A B : Set l} → isBij (≡-Bij {l} {A} {B})

SetExt : ∀ {l} {A B : Set l} → Bij A B → A ≡ B
SetExt = proj₁ SetUni

-- A : Set₀
-- B : Set₁
-- A ≡ B -- не типизируется

record Lift (A : Set₀) : Set₁ where
  constructor lift
  field
    unlift : A

open Lift

strong-SetExt : {A B : Set} → (A ≡ B) ≡ Lift (Bij A B)
strong-SetExt {A} {B} = SetExt ((λ p → lift (≡-Bij p)) , (λ l → SetExt (unlift l)) , let t = proj₂ (SetUni {_} {A} {B}) in proj₁ t , (λ l → cong lift (proj₂ t (unlift l))))

-- 2. Пример использования SetUni.

-- 2a. sort₁, sort₂, isSort sort₁ → isSort sort₂

sort₁ : {A : Set} → List A → List A
sort₁ x = x

sort₂ : {A : Set} → List A → List A
sort₂ x = x

sort₁≡sort₂ : {A : Set} → sort₁ {A} ≡ sort₂ {A}
sort₁≡sort₂ = refl

isSort : {A : Set} → (List A → List A) → Set
isSort _ = ⊤

sort₁-isSort : {A : Set} → isSort {A} sort₁
sort₁-isSort = tt

sort₂-isSort : {A : Set} → isSort {A} sort₂
sort₂-isSort {A} = subst (isSort {A}) sort₁≡sort₂ (sort₁-isSort {A})



DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

ℕ-DecEq : DecEq ℕ
ℕ-DecEq zero zero = yes refl
ℕ-DecEq zero (suc y) = no (λ())
ℕ-DecEq (suc x) zero = no (λ())
ℕ-DecEq (suc x) (suc y) with ℕ-DecEq x y
... | yes p = yes (cong suc p)
... | no p = no (λ x → p (cong pred x))

{-
ℕ≡ℕ⊎ℕ : ℕ ≡ (ℕ ⊎ ℕ)
ℕ≡ℕ⊎ℕ = {!!}

ℕ⊎ℕ-DecEq : DecEq (ℕ ⊎ ℕ)
ℕ⊎ℕ-DecEq = subst DecEq ℕ≡ℕ⊎ℕ ℕ-DecEq
-}

lemma : {A B : Set} → Bij A B → DecEq A → DecEq B
lemma {A} {B} (f , g , p , q) Ad b b' with Ad (g b) (g b')
lemma {A} {B} (f , g , p₁ , q) Ad b b' | yes p = yes (trans (sym (q b)) (trans (cong f p) (q b')))
lemma {A} {B} (f , g , p , q) Ad b b' | no ¬p = no (λ t → ¬p (cong g t))

lemma' : (P : Set → Set) {A B : Set} → Bij A B → P A → P B
lemma' P b = subst P (SetExt b)

-- 3. Set не является множеством.

isInj : ∀ {l k} {A : Set l} {B : Set k} → (A → B) → Set (l Level.⊔ k)
isInj {A = A} f = (x y : A) → f x ≡ f y → x ≡ y

isBij-isInj : ∀ {l k} → {A : Set l} {B : Set k} (f : A → B) → isBij f → isInj f
isBij-isInj f (g , p , _) x x' q = trans (sym (p x)) (trans (cong g q) (p x'))

not-not : (x : Bool) → not (not x) ≡ x
not-not true = refl
not-not false = refl

Set-is-not-a-set : isSet Set → ⊥
Set-is-not-a-set p =
  let t₀ = cong ≡-Bij (p Bool Bool refl (SetExt (not , not , not-not , not-not)))
      t₁ = funExtInv _ _ (cong proj₁ (trans t₀ (proj₂ (proj₂ SetUni) _))) true
  in subst T t₁ tt

-- 4. Аксиома K.

-- K : {A : Set₁} (p : A ≡ A) → p ≡ refl
-- K = ?

-- 5. Группоиды.

-- isProp : Set → Set
-- isProp A = (x y : A) → x ≡ y

-- isSet : Set → Set
-- isSet A = (x y : A) → isProp (x ≡ y)

isGpd : Set → Set
isGpd A = (x y : A) → isSet (x ≡ y)

is-n-Type : ℕ → Set → Set
is-n-Type 0 A = isSet A
is-n-Type (suc n) A = (x y : A) → is-n-Type n (x ≡ y)

idp : {G : Set} {x : G} → x ≡ x
idp = refl

_**_ : {G : Set} {x y z : G} → x ≡ y → y ≡ z → x ≡ z
p ** refl = p

inv : {A : Set} {x y : A} → x ≡ y → y ≡ x
inv = sym

idp-left : {A : Set} {x y : A} (p : x ≡ y) → idp ** p ≡ p
idp-left refl = refl

idp-left-gr : {A : Set} {x : A} (p : x ≡ x) → idp ** p ≡ p
idp-left-gr = idp-left

idp-right : {A : Set} {x y : A} (p : x ≡ y) → p ** idp ≡ p
idp-right refl = refl

**-assoc : {A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ** q) ** r ≡ p ** (q ** r)
**-assoc p q refl = refl

-- 6. Группа автоморфизмов элемента группоида.

-- aut : (G : Set) → isGpd G → G → Set
-- aut G Gp g = g ≡ g

-- 7. Автоморфизмы конечных множеств, разница между ℕ и FinSet.
