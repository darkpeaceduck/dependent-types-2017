module tasks07 where

open import Data.Nat hiding (_≤_)
open import Data.List hiding (filter)
open import Data.Unit hiding (_≤_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty

-- 1. Определите тип бесконечных бинарных деревьев, реализуйте для них функции map и reflect, которая отражает дерево горизонтально.
data bTree (A : Set) : Set where
  btree : (a : A) → bTree A → bTree A → bTree A

map' : {A B : Set} → (A → B) → bTree A → bTree B
map' f (btree a l r) = btree (f a) (map' f l) (map' f r)

reflect' : {A : Set} → bTree A → bTree A
reflect' (btree a l r) = btree a (reflect' r) (reflect' l)
-- 2. Докажите эквивалентность <= и ≤.

_<=_ : ℕ → ℕ → Bool
0 <= _ = true
suc _ <= 0 = false
suc n <= suc k = n <= k

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → 0 ≤ n
  s≤s : {n k : ℕ} → n ≤ k → suc n ≤ suc k

<=-≤ : (n k : ℕ) → T (n <= k) → n ≤ k
<=-≤ 0 x arg = z≤n
<=-≤ (suc x) 0 arg = ⊥-elim arg
<=-≤ (suc x) (suc y) arg = s≤s (<=-≤ x y arg)

≤-<= : {n k : ℕ} → n ≤ k → T (n <= k)
≤-<= z≤n = tt
≤-<= (s≤s arg) = ≤-<= arg

-- 3. Докажите эквивалентность isSorted и isSorted'.

module Sorted₁ (A : Set) (_≤_ : A → A → Set) where
  leqHead : A → List A → Set
  leqHead _ [] = ⊤
  leqHead x (y ∷ _) = x ≤ y

  isSorted : List A → Set
  isSorted [] = ⊤
  isSorted (x ∷ xs) = leqHead x xs × isSorted xs

  data isSorted' : List A → Set where
    nil : isSorted' []
    cons : (x : A) (xs : List A) → leqHead x xs → isSorted' xs → isSorted' (x ∷ xs)
  
  isSorted-isSorted' : (xs : List A) → isSorted xs → isSorted' xs
  isSorted-isSorted' [] res = nil
  isSorted-isSorted' (x  ∷ xs) (a , b) = cons x xs a (isSorted-isSorted' xs b)
  
  isSorted'-isSorted : {xs : List A} → isSorted' xs → isSorted xs
  isSorted'-isSorted nil = tt
  isSorted'-isSorted (cons x xs f fxs) = (f , (isSorted'-isSorted fxs))

-- 4. Определите предикат принадлежности элемента списку.

data _∈_ {A : Set} (a : A) : List A → Set where
  kin : (xs : List A) → a ∈ (a ∷ xs)
  next : (x : A) (xs : List A) → a ∈ xs → a ∈ (x ∷ xs) 

-- 5. Определите предикат xs ⊆ ys, означающий "список xs является подсписком ys".

data _⊆_ {A : Set} : List A → List A → Set where
  kin : (ys : List A) → [] ⊆ ys
  keq : (x : A) (xs ys : List A) → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
  kapp : (y : A) (xs : List A) (ys : List A) → xs ⊆ ys → xs ⊆ (y ∷ ys)
  

-- 6. Докажите, что filter xs ⊆ xs для любого списка xs.
filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if (p x) then x ∷ (filter p xs) else (filter p xs)

lemma : {A : Set} → (p : A → Bool) → (xs : List A) → (filter p xs) ⊆ xs
lemma p [] = kin []
lemma p (x ∷ xs) with p x
... | true = keq x (filter p xs) xs (lemma p xs)
... | false = kapp x (filter p xs) xs (lemma p xs)

-- 7*. Докажите принцип индукции для натуральных чисел, позволяющий использовать индукционную гипотезу для любого меньшего числа.

ℕ-<-ind : (P : ℕ → Set) → ((n : ℕ) → ((k : ℕ) → k < n → P k) → P n) → (n : ℕ) → P n
ℕ-<-ind P h n = {!!}
