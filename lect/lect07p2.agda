module lect07p2 where

open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_≤_; _<_; Ordering; compare)
open import Data.List hiding (zipWith)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum

-- 1. Sorted lists.

module Sorted (A : Set) (_≤_ : A → A → Set) where
  leqHead : A → List A → Set
  leqHead _ [] = ⊤
  leqHead x (y ∷ _) = x ≤ y

  data isSorted : List A → Set where
    nil : isSorted []
    cons : (x : A) (xs : List A) → leqHead x xs → isSorted xs → isSorted (x ∷ xs)

data isPerm {A : Set} : List A → List A → Set where
  perm-nil : isPerm [] []
  perm-cons : {x : A} {xs ys₁ ys₂ : List A} →
              isPerm xs (ys₁ ++ ys₂) →
              isPerm (x ∷ xs) (ys₁ ++ x ∷ ys₂)

module Sort (A : Set) (_≤_ : A → A → Set) (L : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Sorted A (λ x y → x ≤ y)

  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) with L x y
  ... | inj₁ _ = x ∷ y ∷ ys
  ... | inj₂ _ = y ∷ insert x ys

  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

  insert-leqHead-lemma : (x y : A) (xs : List A) → x ≤ y → leqHead x xs → leqHead x (insert y xs)
  insert-leqHead-lemma x y [] p q = p
  insert-leqHead-lemma x y (x₁ ∷ xs) p q with L y x₁
  ... | inj₁ _ = p
  ... | inj₂ _ = q

  insert-isSorted : (x : A) (xs : List A) → isSorted xs → isSorted (insert x xs)
  insert-isSorted x [] p = Sorted.cons x [] tt Sorted.nil
  insert-isSorted x (x₁ ∷ xs) p with L x x₁
  insert-isSorted x (x₁ ∷ xs) p | inj₁ q = Sorted.cons x (x₁ ∷ xs) q p
  insert-isSorted x (x₁ ∷ xs) (Sorted.cons .x₁ .xs x₂ p) | inj₂ q = Sorted.cons x₁ (insert x xs) (insert-leqHead-lemma x₁ x xs q x₂) (insert-isSorted x xs p)

  sort-isSorted : (xs : List A) → isSorted (sort xs)
  sort-isSorted [] = Sorted.nil
  sort-isSorted (x ∷ xs) = insert-isSorted x (sort xs) (sort-isSorted xs)

------------------------------------

{-
data SortedList (A : Set) : Set where
  [] : SortedList A
  cons : (x : A) (xs : SortedList A) (leqHead x xs)
-}

-- 2. Индукция-рекурсия, вселенные.

f : ℕ → ℕ
g : (x : ℕ) → f x ≡ f x → ℕ

f 0 = 0
f (suc n) = g n refl
  
g 0 _ = 0
g (suc n) _ = f (suc n)

{- Нельзя
id : (A : Set) → A → A
id ℕ = suc
id Bool = not
id _ = λ x → x
-}

data U : Set
El : U → Set

data U where
  nat : U
  bool : U
  union : U → U → U
  pi : (A : U) → (El A → U) → U

El nat = ℕ
El bool = Bool
El (union X X₁) = El X ⊎ El X₁
El (pi A B) = (x : El A) → El (B x)

id : (A : U) → El A → El A
id nat = suc
id bool = not
id _ = λ x → x

-- 3. Тип сортированных списков.

-- индукция-рекурсия
module SortedList'' (A : Set) (_≤_ : A → A → Set) where
  data SortedList : Set
  leqHead : A → SortedList → Set

  data SortedList where
    [] : SortedList
    cons : (x : A) (xs : SortedList) → leqHead x xs → SortedList
  
  leqHead x [] = ⊤
  leqHead x (cons x₁ xs x₂) = x ≤ x₁

-- индукция-индукция
module SortedList' (A : Set) (_≤_ : A → A → Set) where
  data SortedList : Set  
  data leqHead (x : A) : SortedList → Set

  data SortedList where
    [] : SortedList
    cons : (x : A) (xs : SortedList) → leqHead x xs → SortedList

  data leqHead x where
    nil : leqHead x []
    cons : (y : A) (xs : SortedList) → x ≤ y → (p : leqHead y xs) → leqHead x (cons y xs p)
