module tasks02 where

open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Agda.Primitive renaming (_⊔_ to _⊔l_)

-- 1a. Реализуйте любой алгоритм сортировки

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
nil ++ ys = ys
(cons x xs) ++ ys = cons x (xs ++ ys)

_==''_ : ℕ → ℕ → Bool
0 =='' 0 = true
suc x =='' suc y = x =='' y
_ =='' _ = false

_==L_ : List ℕ → List ℕ → Bool
nil ==L nil = true
(cons x xs) ==L (cons y ys) = (x =='' y) ∧ (xs ==L ys)
_ ==L _ = false

_==L'_ : List ℕ → List ℕ → Set
nil ==L' nil = ⊤
(cons x xs) ==L' (cons y ys) = T (x =='' y)  ×  (xs ==L' ys)
_ ==L' _ = ⊥

length : {A : Set} → List A → ℕ
length nil = 0
length (cons x xs) = suc (length xs)


module Sort {A : Set} (_<_ : A → A → Bool) where
  extrMin : (xs : List A)  → A  →  List A → A × List A
  extrMin nil x y = (x , y)
  extrMin (cons x xs) min acc = if  min < x then extrMin xs x (cons min acc) else  extrMin xs min (cons x acc)
  sort' : List A → ℕ → List A → List A
  sort' a 0 acc = acc
  sort' nil (suc _) acc = acc
  sort' (cons x xs) (suc l) acc  =  let (min , ys) = extrMin xs x nil in sort' ys l (cons min acc)
  sort : List A → List A
  sort xs = sort' xs (length xs) nil  

-- 1b. Остортируйте следующий список



list : List ℕ
list = cons 3 (cons 1 (cons 4 (cons 2 nil)))

le : ℕ → ℕ → Bool
le 0 (suc _) = true
le a 0 = false
le (suc x) (suc y) = le x y

list-sorted : List ℕ
list-sorted = Sort.sort le list

check : T (list-sorted ==L (cons 1 (cons 2(cons 3 (cons 4 nil)))))
check = tt

-- 2. Докажите ассоциативность дизъюнкции

data Unit : Set where
  unit : Unit

infix 3 _==_
_==_ : Bool → Bool → Bool
true == true = true
true == false = false
false == true = false
false == false = true

∨-assoc : (x y z : Bool) → T ((x ∨ y) ∨ z == x ∨ (y ∨ z))
∨-assoc true y z = tt
∨-assoc false true z = tt
∨-assoc false false true = tt
∨-assoc false false false = tt

-- 3. Докажите, что fac 3 равен 6 и что fac 2 не равен 3.

infix 3 _=='_
_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc _ = false
suc _ ==' zero = false
suc x ==' suc y = x ==' y

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n



fac3=6 : T (fac (suc (suc (suc zero))) ==' suc (suc (suc (suc (suc (suc zero))))))
fac3=6 = tt

fac2≠3 : T (fac (suc (suc zero)) ==' suc (suc (suc zero))) → ⊥
fac2≠3 a = a  

-- 4. Докажите ассоциативность _++_.

self : (x : ℕ) →  T (x =='' x)
self zero = tt
self (suc x) = self x

lem : {x y : Bool} -> T x -> T y -> T (x ∧ y)
lem {false} tx _ = tx
lem {true} {false} _ ty = ty
lem {true} {true} _ _ = tt
self-list : (x : List ℕ) → T(x ==L x)
self-list nil = tt
self-list (cons x' xs) =  lem (self x') (self-list xs)

assoc++ : (x y z : List ℕ) → T(((x ++ y) ++ z) ==L (x ++ (y ++ z)))
assoc++ nil y z = self-list (y ++ z)
assoc++ (cons x xs) y z = lem (self x)  (assoc++ xs y z)

-- 5. Закончите доказательство того, что reverse (reverse xs) == xs.

reverse-acc : {A : Set} → List A → List A → List A
reverse-acc acc nil = acc
reverse-acc acc (cons x xs) = reverse-acc (cons x acc) xs

reverse' : {A : Set} → List A → List A
reverse' = reverse-acc nil

reverse-inv : (acc : List ℕ) (xs : List ℕ) → T (reverse-acc nil (reverse-acc acc xs) ==L (reverse-acc xs acc))
reverse-inv nil nil = self-list (reverse-acc nil nil)
reverse-inv (cons x xs) nil = self-list (reverse-acc (cons x nil) xs)
reverse-inv acc (cons x xs) = reverse-inv (cons x acc) xs 

-- 6. Определите запись Point, который может хранить элементы произвольных типов A и B произвольных уровней.
--    Определите равенство для такого типа Point.

record Point {l} {r} (A : Set l) (B : Set r) : Set (l ⊔l r) where
  constructor point
  field
    x : A
    y : B

_==P_ :  {l r : Level} {A : Set l} {B : Set r} →  (_==A_ : A →  A → Bool) -> (_==B_ : B → B → Bool) → Point A B → Point A B → Bool
_==P_ cpmf cpms (point a b) (point a' b') = (cpmf a a') ∧ (cpms b b')

-- 7. Напишите функцию lookup, которая принимает список и натуральное число и возвращает элемент по заданому индексу.
--    В общем случае эту функцию определить невозможно, т.к. индекс может быть больше, чем число элементов в списке.
--    Поэтому эта функция должна дополнительно еще принимать доказательство того, что индекс находится в допустимых границах.
lookup : (xs : List ℕ) → (i : ℕ) → (T (i ==' i)) → ℕ
lookup = {!!}
