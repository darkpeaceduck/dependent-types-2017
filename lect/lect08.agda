module lect08 where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.Sum

-- 1. Как устроено равенство между натуральными числами, спискаи, функциями, типами, и т.д.?

_=='_ : {A : Set} {B : A → Set} (f g : (x : A) → B x) → Set
_=='_ {A} f g = (x : A) → f x ≡ g x

≡-==' : {A : Set} {B : A → Set} (f g : (x : A) → B x) → f ≡ g → f ==' g
≡-==' f .f refl = λ x → refl

-- =='-≡ : {A : Set} {B : A → Set} (f g : (x : A) → B x) → f ==' g → f ≡ g
-- =='-≡ f g p = {!!}

-- 2. Функциональная экстенсиональность.

postulate
  funExt : {A : Set} (B : A → Set) (f g : (x : A) → B x) → f ==' g → f ≡ g

-- 3. Аксиомы, вычислительность.

postulate
  foo' : true ≡ false

bar : Bool → Set
bar true = ⊤
bar false = ℕ

baz : ℕ
baz = subst bar foo' tt

-- 4. Моноид функций.

record Monoid (A : Set) : Set where
  field
    id : A
    _&_ : A → A → A
    assoc : (x y z : A) → (x & y) & z ≡ x & (y & z)
    id-left : (x : A) → id & x ≡ x
    id-right : (x : A) → x & id ≡ x

fun-Monoid : {A B : Set} → Monoid B → Monoid (A → B)
fun-Monoid {A} {B} m = let open Monoid m in record
               { id = λ _ → id ;
                 _&_ = λ f g x → f x & g x ;
                 assoc = λ f g h → funExt (λ x → B) _ _ (λ x → assoc (f x) (g x) (h x)) ;
                 id-left = λ f → funExt (λ _ → B) _ _ (λ x → id-left (f x)) ;
                 id-right = λ f → funExt (λ _ → B) _ _ (λ x → id-right (f x)) 
               }

-- 5. Подмножества, инъективные функции.

{- Нельзя
0 : Even
suc (suc 0) : Even
suc (suc (suc (suc 0))) : Even
-}

isEven : ℕ → Bool
isEven 0 = true
isEven 1 = false
isEven (suc (suc n)) = isEven n

-- { n : ℕ | T (isEven n) } -- теоретико-множественная нотация
-- Σ (n : ℕ) (T (isEven n)) -- в теории типов записывается так

record Even : Set where
  constructor even
  field
    number : ℕ
    proof : T (isEven number)

Even-inc : Even → ℕ
Even-inc = Even.number

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

T-lem : (b : Bool) (x y : T b) → x ≡ y
T-lem false () y
T-lem true x y = refl

Even-inc-isInj : isInj Even-inc
Even-inc-isInj (even number proof) (even .number proof₁) refl = cong (even number) (T-lem (isEven number) proof proof₁)

Σ-eq : {A : Set} (B : A → Set) (x₁ x₂ : A) (y₁ : B x₁) (y₂ : B x₂) →
  (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
Σ-eq B x₁ .x₁ y₁ .y₁ refl refl = refl

mod3 : ℕ → ℕ
mod3 0 = 0
mod3 1 = 1
mod3 2 = 2
mod3 (suc (suc (suc n))) = mod3 n

mod5 : ℕ → ℕ
mod5 0 = 0
mod5 1 = 1
mod5 2 = 2
mod5 3 = 3
mod5 4 = 4
mod5 (suc (suc (suc (suc (suc n))))) = mod5 n

record MultipleOf3Or5 : Set where
  constructor mul
  field
    number : ℕ
    proof : mod3 number ≡ 0 ⊎ mod5 number ≡ 0

Mul-inc : MultipleOf3Or5 → ℕ
Mul-inc = MultipleOf3Or5.number

-- не верно 
Mul-inc-isInj : isInj Mul-inc
Mul-inc-isInj (mul number proof) (mul .number proof₁) refl = {!!}
