module lect03 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Bool

-- 1. Определить Vec рекурсивно.

-- List : Set → Set

vec : Set → ℕ → Set
vec A zero = ⊤
vec A (suc n) = A × vec A n

list'' : vec ℕ 0
list'' = tt

list : vec ℕ 3
list = 234 , 5873578 , 2343 , tt

-- head : {A : Set} → List A → A
-- head = ?

head' : {A : Set} {n : ℕ} → vec A (suc n) → A
head' (x , _) = x

tail' : {A : Set} {n : ℕ} → vec A (suc n) → vec A n
tail' (_ , xs) = xs

-- 2. Определить Vec индуктивно.

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc n == suc k = n == k

data Vec₂ (A : Set) (n : ℕ) : Set where
  nil : T (n == 0) → Vec₂ A n
  cons : {m : ℕ} → T (n == suc m) → A → Vec₂ A m → Vec₂ A n

-- nil : {A : Set} {n : ℕ} → T (n == 0) → Vec₂ A n
-- cons : {A : Set} {n : ℕ} {m : ℕ} → T (n == suc m) → A → Vec₂ A m → Vec₂ A n

vec1 : Vec₂ ℕ 0
vec1 = nil _

vec2 : Vec₂ ℕ 2
vec2 = cons {m = 1} tt 245345 (cons {m = 0} tt 43666 (nil tt))

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {m : ℕ} → A → Vec A m → Vec A (suc m)

vec1' : Vec ℕ 0
vec1' = nil

vec2' : Vec ℕ 2
vec2' = cons 42545 (cons 42525 nil)

nil'' : {A : Set} → Vec A 0
nil'' = nil

-- vec : Set → ℕ → Set
-- Vec₂ : Set → ℕ → Set
-- Vec : Set → ℕ → Set

-- 3. Определить head, tail и append.

foo : {m : ℕ} → Vec ℕ m → ℕ
foo nil = 0
foo (cons x xs) = x

head : {A : Set} {m : ℕ} → Vec A (suc m) → A
head (cons x _) = x

tail : {A : Set} {m : ℕ} → Vec A (suc m) → Vec A m
tail (cons _ xs) = xs

-- 4. Определить функцию length для Vec.

length : {A : Set} → List A → ℕ
length nil = 0
length (cons x xs) = 1 + length xs

len : {A : Set} {n : ℕ} → Vec A n → ℕ
len {n = n} _ = n

-- 5. Обсудить dot паттерны.

_+'_ : ℕ → ℕ → ℕ
n +' zero = n
n +' suc k = suc (n +' k)

{-
_++_ : {A : Set} {n k : ℕ} → Vec A n → Vec A k → Vec A (n + k)
-- xs ++ nil = xs
-- xs ++ cons y ys = ?
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

reverse : {A : Set} {n : ℕ} → Vec A n → Vec A n
reverse nil = nil
reverse (cons x xs) = reverse xs ++ cons x nil

reverse-acc : {A : Set} {n k : ℕ} → Vec A n → Vec A k → Vec A (k + n) 
reverse-acc acc nil = acc
reverse-acc acc (cons x xs) = reverse-acc (cons x acc) xs -- {!!}
-}

_++_ : {A : Set} (n k : ℕ) → Vec A n → Vec A k → Vec A (n + k)
_++_ 0 k nil ys = ys
_++_ _ k (cons {n} x xs) ys = {!!}

data Vec₃ (A : Set) : ℕ → Set where
  nil : Vec₃ A 0
  cons : (n : ℕ) → A → Vec₃ A n → Vec₃ A (suc n)

head₃ : {A : Set} (n : ℕ) → Vec₃ A (suc n) → A
head₃ n (cons m x xs) = x

tail₃ : {A : Set} (n : ℕ) → Vec₃ A (suc n) → Vec₃ A n
tail₃ n (cons m x xs) = xs

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

tail-fac : {A : Set} (n : ℕ) → Vec₃ A (suc (fac n)) → Vec₃ A (fac n)
tail-fac n (cons .(fac n) x xs) = {!!}

----------------------------------------------------

-- Bad!!!
data Foo : ℕ → Set where
  foo' : (n : ℕ) → Foo (fac n)

bak : (n : ℕ) → Foo (n + 1) → ℕ
bak n x = {!x!}

-- Good!!!
data Foo' (k : ℕ) : Set where
  foo' : (n : ℕ) → T (k == fac n) → Foo' k

baz : (n : ℕ) → Foo' (n + 1) → ℕ
baz n (foo' n₁ x) = zero

data Bar (A : Set) : A → A → Set where
  bar : (n : A) → Bar A n n

-- 7. Fin, toℕ, index

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

zero₁ : Fin 1
zero₁ = zero

foobar : Fin 1 → ℕ
foobar zero = 244
foobar (suc ())

one₁ : Fin 2
one₁ = suc zero

-- zero : Fin 2
-- suc zero : Fin 2

-- zero : Fin 3
-- suc zero : Fin 3
-- suc (suc zero) : Fin 3

lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
lookup nil ()
lookup (cons x xs) zero = x
lookup (cons x xs) (suc i) = lookup xs i

toℕ : {n : ℕ} → Fin n → ℕ
toℕ zero = zero
toℕ (suc x) = suc (toℕ x)
