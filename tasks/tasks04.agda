module tasks04 where

open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Data.Sum
open import Data.Unit
open import Data.Bool
open import Data.Vec hiding (reverse) renaming (_++_ to _+V+_)
open import Data.List hiding (reverse) renaming (_++_ to _+L+_)
open import Relation.Binary.PropositionalEquality hiding (cong₂)

-- 1. Докажите следующий факт.

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

_==_ : (ℕ → ℕ) → (ℕ → ℕ) → Set
f == g = (x : ℕ) → f x ≡ g x

D : ℕ → Set
D (suc zero) = ⊤
D (suc (suc zero)) = ⊥
D _ = ⊤

lem : fac == suc → ⊥
lem f = subst D (f (suc zero)) tt

-- 2. Определите симметричность, транзитивность и конгруэнтность при помощи паттерн матчинга.

sym' : {A : Set} {a a' : A} → a ≡ a' → a' ≡ a
sym' refl = refl 

trans' : {A : Set} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans' refl refl = refl

cong' : {A B : Set} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
cong' f refl = refl

-- 3. Определите конгруэнтность для функций двух аргументов через subst.

cong₂ : {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f {a} {a'} {b} {b'} aa bb = subst (λ x → f a b ≡ f a' x) bb (subst (λ x → f a b ≡ f x b) aa refl )  

-- 4. Докажите, что subst эквивалентен cong + repl

repl : {A B : Set} → A ≡ B → A → B
repl refl a = a

-- cong через subst был доказан на лекции.

-- Докажите repl через subst.

repl' : {A B : Set} → A ≡ B → A → B
repl' arg a = subst (λ x → x) arg a   

-- Дркажите subst через repl и cong.

subst' : {A : Set} (B : A → Set) {x y : A} → x ≡ y → B x → B y
subst' f refl bx = repl (cong f refl) bx

-- 5. Докажите дистрибутивность умножения над сложением для натуральных чисел.

open ≡-Reasoning

+-assoc : (x : ℕ) {y z : ℕ} → (x + y) + z ≡ x + (y + z)
+-assoc zero = refl
+-assoc (suc x) = cong suc (+-assoc x)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (sym (+-comm x y))) (+-comm (suc x) y)))


lem1 : (x a : ℕ) →  x * a  + a ≡ (suc x) * a
lem1 zero zero = refl
lem1 zero (suc a) =  (+-comm (0 * (suc a)) (suc a)) 
lem1 (suc x) a = ( 
  begin
    (suc x) * a + a 
  ≡⟨(+-assoc a {x * a} {a})⟩
    a + ((x * a) + a)
  ≡⟨ (cong (λ arg → a + arg) (lem1 x a))⟩
    a + (suc x) * a
  ∎) 
  


distr : (n m k : ℕ) → n * (m + k) ≡ n * m + n * k
distr zero m k = refl
distr (suc x) y z = (
  begin
    (suc x) * (y + z)
  ≡⟨ sym (lem1 x (y + z))⟩
    x * (y + z) + (y + z)
  ≡⟨ (cong (λ a → a + (y + z)) (distr x y z))⟩
    (x * y + x * z) + (y + z)
  ≡⟨ (+-assoc (x * y) {x * z} {y + z})⟩
    x * y + (x * z + (y + z))
  ≡⟨ (cong (λ a → x * y + (x * z + a)) (+-comm y z))⟩
    x * y + (x * z + (z + y))
  ≡⟨ (cong (λ a → x * y + a) ( sym (+-assoc (x * z) {z} {y}))) ⟩
    x * y + ((x * z + z) + y)
  ≡⟨ (cong (λ a → x * y + (a + y)) (lem1 x z)) ⟩
    x * y + (suc x * z + y)
  ≡⟨ (cong (λ a → x * y + a) (+-comm (suc x * z) (y))) ⟩
    x * y + (y + suc x * z)
  ≡⟨( sym (+-assoc (x * y) {y} {(suc x) * z})) ⟩
    (x * y + y) + (suc x * z)
   ≡⟨ (cong (λ a → a +  (suc x * z)) (lem1 x y)) ⟩
    (suc x * y) + (suc x * z)
  ∎)
  
  
-- 6. Докажите следующее утверждение.

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs +L+ x ∷ []

lem5 : {A : Set} (x : A) (xs : List A) →  x ∷ (reverse xs) ≡ reverse (xs +L+ x ∷ [])
lem5 x [] = refl
lem5 a (x ∷ xs) = (cong (λ a → a +L+ (x ∷ [])) (lem5  a xs))

reverse-inv : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-inv [] = refl
reverse-inv (x ∷ xs) = sym (trans (sym (cong (λ a → x ∷ a) (reverse-inv xs))) (lem5 x  (reverse (xs))))
    
-- 7. 
lem6 : {A : Set}  (xs ys : List A) (x : A) → (((ys +L+ (reverse xs)) +L+  (x ∷ [])) ≡  ((ys +L+ (reverse (x ∷ xs)))))
lem6 xs [] x = refl
lem6 xs (y ∷  ys)  x = cong (λ a → (y ∷ a)) (lem6 xs ys x) 

lem7 : {A : Set}  (ys : List A)  → (ys ≡ ys +L+ [])
lem7 [] = refl
lem7 (y ∷  ys) = sym (cong (λ a → y ∷ a) (sym (lem7 ys)))

reverse-append : {A : Set} (xs ys : List A) → reverse (xs +L+ ys) ≡ reverse ys +L+ reverse xs
reverse-append (x ∷ xs) ys = trans (trans (cong reverse (trans (cong (λ a -> x ∷ a) (trans (sym (reverse-inv (xs +L+ ys))) (cong reverse (reverse-append xs ys)))) (lem5 x ((reverse ys) +L+ (reverse xs))))) (reverse-inv (((reverse ys) +L+ (reverse xs)) +L+ (x ∷ [])))) (lem6 xs (reverse ys) x)
reverse-append [] ys = (lem7 (reverse ys))


-- 8. Докажите, что [] является нейтральным элементом для ++.

[]-is-neutral : {A : Set} {n : ℕ} (xs : Vec A n) → subst (Vec A) (+-comm n 0) (xs +V+ []) ≡ xs
[]-is-neutral  = {!!}

-- 9. Докажите, что [] не равно x ∷ xs при помощи паттер матчинга.

List-diff : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff _ _ ()

-- 10. Докажите, что [] не равно x ∷ xs при помощи subst.

D' : {A : Set} (x : List A) → Set
D' [] = ⊤
D' (x ∷ xs)  = ⊥

List-diff' : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff' x xs f = subst D' f tt 
