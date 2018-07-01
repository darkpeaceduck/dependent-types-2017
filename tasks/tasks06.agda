module tasks06 where

open import Data.Nat hiding (_<_)
open import Data.List hiding (filter)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty
open import Agda.Builtin.Unit 

-- 1. Реализуйте любой алгоритм сортировки, используя with для паттерн матчинга на результате сравнения элементов списка.

-- 2. Определите filter через if, а не через with.
--    Докажите для этой версии filter следующую лемму:

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if (p x) then (x ∷ (filter p xs)) else filter p xs

<=-suc : {n m : ℕ} → n ≤ m → n ≤ suc m
<=-suc {0} {0}  _ = z≤n
<=-suc {suc x} {0} ()
<=-suc {0} {suc m} f = z≤n
<=-suc {suc n} {suc m} (s≤s f) = s≤s (<=-suc f)

filter-lem : {A : Set} (p : A → Bool) (xs : List A) → length (filter p xs) ≤ length xs
filter-lem p [] =  z≤n
filter-lem p (x ∷ xs) with p x
... | true = s≤s (filter-lem p xs)
... | false = <=-suc (filter-lem p xs)
-- 3. Докажите, что если равенство элементов A разрешимо, то и равенство элементов List A тоже разрешимо.

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

List-Dec : {A : Set} → DecEq A → DecEq (List A)
List-Dec {A}  p []  []  = yes refl
List-Dec {A}  p (x' ∷ xs)  [] = no (λ ())
List-Dec {A}  p [] (y' ∷ _) =  no (λ ())
List-Dec {A} p (x' ∷ xs) (y' ∷ ys) with List-Dec p xs ys
... | no arg = no (λ o   → arg (cong (drop 1) o))  
... | yes arg with p x' y'
... | no arg' = no (λ o → arg' (cong₂ (λ {(q' ∷  _) q → q' ; _ _ → x' }) o arg)) 
... | yes arg' = yes  (cong₂ (_∷_) arg' arg)



-- 4. Докажите, что предикат isEven разрешим.

DecPred : {A : Set} → (A → Set) → Set
DecPred {A} P = (a : A) → Dec (P a)

isEven : ℕ → Set
isEven n = Σ ℕ (λ k → n ≡ k * 2)

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)


isEven-Dec : DecPred isEven
isEven-Dec n with parity n
isEven-Dec  (.(k * 2)) | even k = yes ( k , refl)
isEven-Dec (.(suc (k * 2))) | odd k =  no (λ p → par-lem k (proj₁ p) (proj₂ p))
  where
    par-lem : (n k : ℕ) → suc (n * 2) ≡ k * 2 → ⊥
    par-lem zero zero ()
    par-lem zero (suc k₁) ()
    par-lem (suc n) zero ()
    par-lem (suc n) (suc k₁) p = par-lem n k₁ (cong pred (cong pred p))


-- 5. Докажите, что если равенство элементов A разрешимо, то любой список элементов A либо пуст, либо состоит из повторений одного элемента, либо в A существует два различных элемента.
repeat : {A : Set} → ℕ → A → List A
repeat zero a = []
repeat (suc n) a = a ∷ repeat n a

data Result (A : Set) (xs : List A) : Set where
  empty : xs ≡ [] → Result A xs
  repeated : (n : ℕ) (a : A) → xs ≡ repeat n a → Result A xs
  A-is-not-trivial : (a a' : A) → ¬ (a ≡ a') → Result A xs

lemma : {A : Set} (xs : List A) → DecEq A → Result A xs
lemma [] p = empty (refl)
lemma (x ∷ xs) p with lemma xs p
... | empty arg = repeated 1 x (cong (λ a → x ∷ a) arg)
... | repeated n a arg with p x a
... | yes eq rewrite eq = repeated (suc n) a (cong (λ a' → a ∷ a') arg)
... | no f  =  A-is-not-trivial x a f
lemma (x ∷ xs) p | A-is-not-trivial a a' f = A-is-not-trivial a a' f
-- 6. Определите view, представляющий число в виде частного и остатка от деления его на произвольное (неотрицательное) число m.
--    Реализуйте функцию деления.

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc x < suc y = x < y

<-Dec : (x : ℕ) -> (y : ℕ) -> Dec (T (x < y))
<-Dec 0 0 = no (λ ())
<-Dec (suc x) 0 = <-Dec x 0
<-Dec 0 (suc y) = yes (tt)
<-Dec (suc x) (suc y) = <-Dec x y

lem1 : (r : ℕ) (m : ℕ) → T (r < (suc m)) →  ¬ T (r < m) → (r ≡ m)
lem1 0 0 eq neq = refl
lem1 (suc r) 0 ()
lem1 0 (suc q) eq neq = ⊥-elim (neq tt)
lem1 (suc r) (suc m) eq neq = cong (suc) (lem1 r m eq neq)

data ModView (m : ℕ) : ℕ → Set where
  quot-rem : ∀ q r → T (r < m) → ModView m (r + q * m)

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

mod-view : (m n : ℕ) → T (isPos m) → ModView m n
mod-view 0 n t  = ⊥-elim t
mod-view ((suc m)) 0 t = quot-rem 0 0 tt
mod-view ( (suc m)) (suc n) t with mod-view ((suc m)) n tt
mod-view ((suc m)) (suc  .(r + q *  (suc m))) t |   quot-rem q r arg  with <-Dec r ( m)
... | yes arg' = quot-rem q (suc r) arg'  
... | no f rewrite (lem1 r ( m) arg f) = quot-rem (suc q) 0 t

div : ℕ → (m : ℕ) → T (isPos m) → ℕ
div n m p with mod-view m n p
div .(r + q * m) m t | quot-rem q r arg = q

div-test : ((div 10 2 tt ) ≡ 5)
div-test = refl

div-test2 : ((div 17 5 tt ) ≡ 3)
div-test2 = refl
