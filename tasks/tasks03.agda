module tasks03 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Empty
open import Data.Maybe

-- 1. Реализуйте аналоги функции replicate для vec и Vec (эта функция создает список заданной длины, состоящий из повторений данного элемента).
vec : Set → ℕ → Set
vec A 0 = ⊤
vec A (suc n) = A × vec A n

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

replicate' : {A : Set} → (n : ℕ) → (a : A) → vec A n
replicate' 0 a = tt
replicate' (suc n) a = (a , replicate' n a)

replicate'' : {A : Set} → (n : ℕ) → (a : A) → Vec A n
replicate'' 0 a = nil
replicate'' (suc n) a = cons a (replicate'' n a)
-- 2. Реализуйте аналоги функции map для vec и Vec.
map' : {A B : Set} {n : ℕ} → (A → B) → vec A n → vec B n
map' {B = B} {n = zero} f tt = tt
map' {B = B} {n = suc x} f (y , xs) = (f y , map' f xs)

map'' : {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
map'' f nil = nil
map'' f (cons x xs) = cons (f x) (map'' f xs)

-- 3. Реализуйте аналоги функции zipWith для vec и Vec.
--    Функция должна принимать вектора одинаковой длины.
fzip :  {A B : Set} {n : ℕ} → vec (A → B) n → vec A n → vec B n
fzip {n = zero} tt tt = tt
fzip {n = suc x} (f , fs) (a , as) = (f a , fzip fs as)

zipWith' : {A B C : Set} {n : ℕ} → (A → B → C) → vec A n → vec B n → vec C n
zipWith'  {A} {B} {C} {n} f  a b = fzip {B} {C} {n} (map' (λ a' → f a') a) b

fzip' :  {A B : Set} {n : ℕ} → Vec (A → B) n → Vec A n → Vec B n
fzip' {n = zero} nil nil = nil
fzip' {n = suc x} (cons f fs) (cons a as) = cons (f a)  (fzip' fs as)

zipWith'' : {A B C : Set} {n : ℕ} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith''  {A} {B} {C} {n} f  a b = fzip' {B} {C} {n} (map'' (λ a' → f a') a) b 

-- 4. Реализуйте Fin как рекурсивную функцию.
Fin' : ℕ → Set
Fin' 0 = ⊥
Fin' 1 = Maybe ℕ
Fin' (suc x) = (Maybe ℕ) × Fin' x


-- 5. Функции Fin n → A соответствуют спискам элементов A длины n.
--    Функция, преобразующие Vec A n в Fin n → A была реализована на лекции.
--    Реализуйте обратную функцию.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

coina :  {n : ℕ} {m : ℕ}  →  (Fin (suc m))
coina {m = zero} = zero {zero}
coina {n = zero} {m = m} = zero {m}
coina {n = suc (n')} {m = suc(m)} = suc (coina {n'} {m = m} )

de :  {m : ℕ}  → Fin m → Fin (suc m)
de {m = suc(m)} zero = zero {suc(m)}
de (suc xs) = suc (de xs)

coinb :  {A : Set} {m : ℕ}  → (Fin (suc m) → A) →  Fin m → A
coinb f arg = f (de arg)  

coin : {A : Set} {n : ℕ} → (Fin n → A) → Vec A n
coin {n = zero} f = nil
coin {n = suc (m)} f = cons  (f (coina {m} {m})) (coin (coinb  f))


-- 6. Определите тип матриц и ряд функций над ними.

Mat : Set → ℕ → ℕ → Set
Mat A 0 y = ⊤
Mat A (suc x) y = (Vec A y) × (Mat A x y)

app : {A : Set} →(m : ℕ) → {n : ℕ} → Mat A m n → Vec A m → Mat A m (suc n)
app zero tt _ = tt
app (suc n) (v , p) (cons y ys) = ((cons y v) , app n p ys)

-- диагональная матрица с элементами e на диагонали и z на остальных позициях.

diag : {A : Set} → A → A → {n : ℕ} → Mat A n n
diag z e {n = zero} = tt
diag z e {n = suc n} = (cons e (replicate'' n z) , app n (diag z e {n}) (replicate'' n z))


-- транспонирование матриц

transpose : {A : Set} {n m : ℕ} → Mat A n m → Mat A m n
transpose {n} {m = zero} M = tt
transpose {n = zero} {m = suc m} M = (nil , transpose {n = 0} {m = m} M)
transpose {n = suc n} {m = suc m} (v , p) = app (suc m) (transpose p) v 

-- сложение матриц

add : {A : Set} (_+_ : A → A → A) → {n m : ℕ} → Mat A n m → Mat A n m → Mat A n m
add _+_ {zero} {x} a b = tt
add _+_ {suc n} {x} (v , p) (v' , p') = ( zipWith'' _+_  v v' , add _+_ p p') 

-- умножение матриц

produce'' : {A  : Set} → (n : ℕ) → (A → A → A) → Vec A (suc n) → A
produce'' zero _ (cons x _) = x
produce'' (suc n) f (cons x xs) = f x (produce'' n f xs)

mulh : {A : Set} (_+_ _*_ : A → A → A) → {m k : ℕ}  → Vec A (suc m) → Mat A k (suc m) → Vec A k
mulh _+_ _*_ {m} {k = zero} _ _ = nil
mulh  _+_ _*_ {m} {suc k} v ( v' , p ) = cons (produce'' m _+_ (zipWith'' _*_ v v')) (mulh _+_ _*_ v p)  


mul' : {A : Set} (_+_ _*_ : A → A → A) → {n m k : ℕ} →  Mat A n (suc m) → Mat A k (suc m) → Mat A n k
mul' _+_ _*_ {n = 0} {k = k} A B = tt
mul' _+_ _*_ {n = suc n} {k = zero} (v , p) B = (nil , mul' _+_ _*_ p B)  
mul' _+_ _*_ {n = suc n} {k = suc k} (v , p) B = ( mulh _+_ _*_  v  B   , mul' _+_ _*_ p B) 

mul : {A : Set} (_+_ _*_ : A → A → A) → {n m k : ℕ} → Mat A n (suc m) → Mat A (suc m) k → Mat A n k
mul _+_ _*_ M N = mul' _+_ _*_ M (transpose N) 

-- 7. Определите при помощи индуктивных семейств тип CTree A n бинарных деревьев высоты ровно n с элементами во внутренних узлах.
--    Любое такое бинарное дерево будет полным.

data CTree (A : Set) : ℕ → Set where
  leaf : CTree A 0
  node : {m : ℕ} → A → CTree A m →  CTree A m →  CTree A (suc m)

-- 8. Определите при помощи индуктивных семейств тип Tree A n бинарных деревьев высоты не больше n с элементами во внутренних узлах.


data Tree (A : Set) : ℕ → Set where
  leaf : {m : ℕ} → Tree A m
  node : {m : ℕ} → A → Tree A m →  Tree A m →  Tree A (suc m)

-- определите функцию, возвращающую высоту дерева.
max : {n : ℕ}  → Fin (n) → Fin ( n) → Fin ( n)
max (zero) x = x
max x zero = x
max (suc x) (suc y)  = suc (max x y)

height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
height n (leaf) = zero {n}
height (suc n) (node v t1 t2) = suc ( max (height n t1) (height n t2))

