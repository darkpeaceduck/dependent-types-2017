module lect01 where

-- 1. Bool, not, ||, if then else

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

infixl 6 _||_
_||_ : Bool -> Bool -> Bool
true || true = true
_ || _ = false

-- 2. Nat, +, *

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

if_then_else_ : Bool -> Nat -> Nat -> Nat
if true then x else y = x
if false then x else y = y

_+_ : Nat -> Nat -> Nat
x + zero = x
x + suc y = suc (x + y)

_*_ : Nat -> Nat -> Nat
x * zero = zero
x * suc y = x + (x * y)

-- 3. Termination, div

f : Nat -> Nat
f zero = zero
f (suc zero) = zero
f (suc (suc x)) = x

_-_ : Nat → Nat → Nat
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

_<_ : Nat → Nat → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

div : Nat -> Nat -> Nat
div x y = div' x x y
  where
    div' : Nat -> Nat → Nat → Nat
    div' zero _ _ = zero
    div' (suc n) x y = if (x < y) then zero else suc (div' n (x - y) y)

{-
g : Nat -> Nat -> Nat
g (suc x) (suc y) = g x (y * y) + g (x * x) y
g _ _ = zero
-}

-- 4. Полиморфизм, id, неявные аргументы

id : (a : Set) -> a -> a
id _ x = x

h = id Nat zero
h' = id Bool true

const : {A : Set} -> A -> {B : Set} -> B -> A
const {A} a _ = a

h'' = const zero

h''' = h'' zero
