module tasks01 where

-- 0. Напишите на хаскеле тип, соответствующий следующим формулам, и предъявите элемент этого типа (тем самым доказав, что эта формула верна):
-- a. (P -> R) -> (Q -> R) -> P or Q -> R
-- b. (P and Q -> R) -> P -> Q -> R
-- c. (P -> Q -> R) -> P and Q -> R
-- d. (P or Q -> P and Q) -> (P -> Q) and (Q -> P)
-- e. ((P -> Q -> R) -> P) -> (P -> R) -> R
-- f. ((((P -> Q) -> P) -> P) -> Q) -> Q

-- [ See task0.hs ]

-- 1. Определите flip, композицию
flip : {a b c : Set} → (a -> b -> c) -> b -> a -> c
flip f b a = f a b

compose : {a b c : Set} → (a → b) → (c → a) → c → b
compose f g c = f (g c) 

-- 2. Определите миксфикссный if_then_else_ полиморфный по возвращаемому значению

data Bool : Set where
    true false : Bool

not : Bool → Bool
not true = false
not false = true

infix 7 _||_
_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

if_then_else_ : Bool -> {a : Set} -> a -> a -> a
if true then x else y = x
if false then x else y = y

-- 3. Определите возведение в степень и факториал для натуральных чисел

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

infix 5 _+_
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

infix 6 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + x * y

_^_ : ℕ → ℕ → ℕ
x ^ zero = suc zero
y ^ suc x = y * (y ^ x)

fac : ℕ → ℕ
fac zero = suc zero
fac (suc x) = (suc x) * (fac x)

-- 4. Определите mod и gcd

_-_ : ℕ → ℕ → ℕ
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y


div' : ℕ → ℕ → ℕ → ℕ
div' zero x y = zero
div' (suc c) x y = if (x < y) then zero else suc (div' c (x - y) y)

div : ℕ → ℕ → ℕ
div x y = div' x x y

mod : ℕ → ℕ → ℕ
mod x y = x - (y * (div x y)) 

gcd' : ℕ → ℕ → ℕ → ℕ
gcd' zero x y = x
gcd' (suc c) x zero = x
gcd' (suc c) x y = gcd' c y (mod x y)

gcd : ℕ → ℕ → ℕ
gcd a b = gcd' a a b
