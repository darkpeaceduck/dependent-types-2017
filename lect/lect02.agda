module lect02 where

-- 1. Списки, append

infixr 5 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- 2. type LN = List ℕ?

open import Data.Nat

LN = List ℕ

foo''' : Set → Set
foo''' A = List (List A)

-- 3. Модули, open, import, hiding, renaming

module M where
  f : ℕ → ℕ
  f x = x

open M

g = f

open import Data.Unit
open import Data.Bool hiding (T)
open import Data.Nat
-- open import Data.List renaming (length to len)

module Sort {A : Set} (_<_ : A → A → Bool) where
  sort : List A → List A
  sort xs = xs

  xx : A → A → ℕ
  xx a b = if a < b then 0 else 1

-- Просто для примера
_<<_ : ℕ → ℕ → Bool
_<<_ _ _ = false

-- open Sort _<<_

module X = Sort _<<_

open X

foobar : List ℕ → List ℕ
foobar = sort

list : List ℕ
list = 1 ∷ 2 ∷ 3 ∷ []

ff = sort list

-- 4. Пустой и одноэлементный типы

data Empty : Set where

--  ⊥   ⊤

absurd : {A : Set} → Empty → A
absurd ()

foo' : List Empty → ℕ
foo' [] = 0
foo' (() ∷ xs)

xxx : {A : Set} → (ℕ → Empty) → A
xxx f = absurd (f 0)

data Unit : Set where
  tt : Unit

yyy : Unit
yyy = tt

-- 5. Пример утверждений и доказательств, not (not x) == x

infix 3 _==_
_==_ : Bool → Bool → Bool
true == true = true
false == false = true
_ == _ = false

T : Bool → Set
T true = Unit
T false = Empty

hhh : T true
hhh = tt

not-inv : (x : Bool) → T (not (not x) == x)
not-inv false = hhh
not-inv true = tt

not-inv' : (x : Bool) → T (not x == x) → Empty
not-inv' false b = b
not-inv' true b = b



-- 6. Type checking

infixl 4 _&&_
_&&_ : Bool → Bool → Bool
-- _ && false = false
-- x && true = x
-- false && _ = false
-- true && y = y

true && true = true
false && true = false
true && false = false
false && false = false

foo : T (true && false == true) → Empty
foo x = x

baz : (x : Bool) → T (x && false == false)
baz false = tt
baz true = tt

baz' : (x : Bool) → T (false && x == false)
baz' x = {!!}

-- 7. Еще примеры утверждений и доказательств: ассоциативность сложения натуральных чисел, инволютивность reverse.

infix 1 _==''_
_==''_ : ℕ → ℕ → Bool
0 =='' 0 = true
suc x =='' suc y = x =='' y
_ =='' _ = false

=='-isRefl : (n : ℕ) → T (n =='' n)
=='-isRefl zero = tt
=='-isRefl (suc n) = =='-isRefl n

assoc+ : (x y z : ℕ) → T ((x + y) + z =='' x + (y + z))
assoc+ zero y z = =='-isRefl (y + z)
assoc+ (suc x) y z = assoc+ x y z


reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

_==L_ : List ℕ → List ℕ → Bool
[] ==L [] = true
(x ∷ xs) ==L (y ∷ ys) = (x =='' y) && (xs ==L ys)
_ ==L _ = false

reverse-acc : {A : Set} → List A → List A → List A
reverse-acc acc [] = acc
reverse-acc acc (x ∷ xs) = reverse-acc (x ∷ acc) xs

reverse' : {A : Set} → List A → List A
reverse' = reverse-acc []

reverse-inv : (acc : List ℕ) (xs : List ℕ) → T (reverse-acc [] (reverse-acc acc xs) ==L (reverse-acc acc xs))
reverse-inv acc [] = tt
reverse-inv acc (x ∷ xs) = {!!}
