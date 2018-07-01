module tasks08 where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.List hiding (filter)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Relation.Nullary
open import Data.Maybe

-- 1*. Докажите, что алгоритм сортировки, определенный ниже, корректен.

module Sorted (A : Set) (_≤_ : A → A → Set) where
  leqHead : A → List A → Set
  leqHead _ [] = ⊤
  leqHead x (y ∷ _) = x ≤ y

  data isSorted : List A → Set where
    nil : isSorted []
    cons : (x : A) (xs : List A) → leqHead x xs → isSorted xs → isSorted (x ∷ xs)

module Perm (A : Set) where
  data isPerm : List A → List A → Set where
    nil : isPerm [] []
    cons : (x : A) (xs ys ys₁ ys₂ : List A) → isPerm xs (ys₁ ++ ys₂) → ys ≡ ys₁ ++ x ∷ ys₂ → isPerm (x ∷ xs) ys

  -- Вам, возможно, понадобятся эти леммы.
  isPerm-++-left : {xs ys : List A} → isPerm xs ys → (zs : List A) → isPerm (xs ++ zs) (ys ++ zs)
  isPerm-++-left p zs = {!!}

  isPerm-++-right : {xs ys : List A} (zs : List A) → isPerm xs ys → isPerm (zs ++ xs) (zs ++ ys)
  isPerm-++-right zs p = {!!}

  isPerm-trans : {xs ys zs : List A} → isPerm xs ys → isPerm ys zs → isPerm xs zs
  isPerm-trans p q = {!!}

  isPerm-++ : {xs₁ xs₂ ys₁ ys₂ : List A} → isPerm xs₁ ys₁ → isPerm xs₂ ys₂ → isPerm (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  isPerm-++ {xs₁} {xs₂} {ys₁} {ys₂} p q = isPerm-trans (isPerm-++-left p xs₂) (isPerm-++-right ys₁ q)

module Sort (A : Set) (_≤_ : A → A → Set) (L : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Sorted A (λ x y → x ≤ y)
  open Perm A

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

  sort-isPerm : (xs : List A) → isPerm xs (sort xs)
  sort-isPerm = {!!}

-- 2. Определите тип бинарных сортированных деревьев.
--    То есть таких деревьев, в которых для любого узла верно, что все элементы в левом поддереве меньше либо равны, чем значение в узле, которое меньше либо равно, чем все элементы в правом поддереве.

module BinSortedTrees (A : Set) (_≤_ : A → A → Set) (L  : (x y : A) → x ≤ y ⊎ y ≤ x)  where
  data BinSortedTree : Set
  leqTree : A → BinSortedTree → Set
  reqTree : A → BinSortedTree → Set

  data BinSortedTree  where
    leaf : (a : A) → BinSortedTree
    node : (x : A) → (l : BinSortedTree) → (r : BinSortedTree) → (leqTree x r) →  (reqTree x l) → BinSortedTree

  getMin : A → A → A
  getMin a b with L a b
  ... | inj₁ _ = a
  ... | inj₂ _ = b

  getMax : A → A → A
  getMax a b with L a b
  ... | inj₁ _ = b
  ... | inj₂ _ = a

  fMin : BinSortedTree → A
  fMin (leaf y) = y
  fMin (node y l r ll rr) = getMin y (getMin (fMin l) (fMin r))

  fMax : BinSortedTree → A
  fMax (leaf y) = y
  fMax (node y l r ll rr) = getMax y (getMax (fMax l) (fMax r))
  
  leqTree x (leaf y) = x ≤ y
  leqTree x tree = x ≤ (fMin tree) 

  reqTree x (leaf y) = y ≤ x
  reqTree x tree = (fMax tree) ≤ x

-- 3. Реализуйте функцию сортировки, возвращающую SortedList.

module SortedList (A : Set) (_≤_ : A → A → Set) (L : (x y : A) → x ≤ y ⊎ y ≤ x) where
  data SortedList : Set
  leqHead : A → SortedList → Set

  data SortedList where
    [] : SortedList
    cons : (x : A) (xs : SortedList) → leqHead x xs → SortedList

  leqHead x [] = ⊤
  leqHead x (cons x₁ xs x₂) = x ≤ x₁

  data ApList : A → A → Set where
     nil : (a : A) → ApList a a
     cons : {q b : A} (a : A) → (xs : ApList q b) → a ≤ q  → ApList a b

  data RApList : A  → Set where
     nil : (a : A) → RApList a
     cons : {b : A} (a : A) → (xs : RApList b) → b ≤ a  → RApList a
  
  append' : {q B : A} →  (ApList q B) → (a : A) → (B ≤ a) → ApList q a
  append' (nil v) a ba = cons v (nil a) ba
  append' (cons x xs pxs) a ba = cons x (append' xs a ba) pxs
  
  tr2 : {q B b : A} → (ApList q B) → RApList b → (b ≤ q) →  (RApList B)
  tr2 (nil v) acc p = cons v acc p
  tr2 (cons x xs dno) acc p = tr2 xs (cons x acc p) dno
 

  tr' : {B : A} → RApList B → (xs : SortedList) →  (leqHead B xs) → SortedList
  tr' (cons x xs dno) acc p = tr' xs (cons x acc p) dno
  tr' (nil v) acc p = cons v acc p

  tr : {q B : A} →  (ApList q B)  → SortedList
  tr (cons x xs dno) = tr' (tr2 xs (nil x) dno) [] tt
  tr (nil v) = cons v [] tt

  mmm : {q B  : A} →  (ApList q B) → (xs : SortedList) → (leqHead B xs)  → (SortedList)
  mmm acc [] _  = tr acc
  mmm acc (cons x xs pxs) p = mmm (append' acc x p) xs pxs  

  step : {q B  : A} →  (ApList q B) → (a : A) → (B ≤ a)  → (xs : SortedList) → (leqHead B xs) →  SortedList
  step acc a ba [] _ = tr (append' acc a ba)
  step acc a ba (cons y ys pys) bb with L a y
  ... | inj₂ ya = step (append' acc y bb) a ya ys pys
  ... | inj₁ ay = mmm (append' acc a ba) (cons y ys pys) ay

  sinsert : (a : A) → (xs : SortedList) → SortedList
  sinsert  a [] = cons a [] tt
  sinsert a (cons x xs pxs) with L a x
  ... | inj₁ ax = cons a (cons x xs pxs) ax
  ... | inj₂ xa = step (nil x) a xa xs pxs

  sort : List A → SortedList
  sort [] = []
  sort (x ∷ xs) = sinsert x (sort xs)


-- 4. Доказате, что трансформер StateT сохраняет функториальность.

postulate
  funExt : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) →
      fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

StateT : Set → (Set → Set) → (Set → Set)
StateT S F A = A → F (A × S)

StateT-Functor : (S : Set) (F : Set → Set) → Functor F → Functor (StateT S F)
StateT-Functor S F p = record
                   { fmap = fmap
                     ; fmap-id = {!!}
                     ; fmap-comp = {!!}
               } where
               fmap :  {A B : Set} → (A → B) → (StateT S F) A → (StateT S F) B
               fmap f sfa st =  {!!}
-- 5. Пусть f : A → B и g : B → C ─ некоторые функции.
--    Докажите, что если f и g инъективны, то g ∘ f также инъективна.
--    Докажите, что если g ∘ f инъективна, то f также инъективна.

isInj : {A B : Set} → (A → B) → Set
isInj {A} {B} f = (x x' : A) → f x ≡ f x' → x ≡ x'

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

∘-inj : {A B C : Set} (f : A → B) (g : B → C) → isInj f → isInj g → isInj (g ∘ f)
∘-inj f g fi gi x x' gfxx' = fi x x' (gi (f x) (f x') gfxx')

∘-inj' : {A B C : Set} (f : A → B) (g : B → C) → isInj (g ∘ f) → isInj f
∘-inj' f g igf x x' fxx' = igf x x' (cong g fxx')

-- 6. Определите предикат "делится на 3 или на 5" так, чтобы он возвращал утверждения.
--    Докажите, что MultipleOf3Or5 вкладывается в ℕ.

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

mod5 : ℕ → Bool
mod5 0 = true
mod5 1 = false
mod5 2 = false
mod5 3 = false
mod5 4 = false
mod5 (suc (suc (suc (suc (suc n))))) = mod5 n


mod3 : ℕ → Bool
mod3 0 = true
mod3 1 = false
mod3 2 = false
mod3 (suc (suc (suc n))) = mod3 n

isMultipleOf3Or5 : ℕ → Set
isMultipleOf3Or5 n = T ((mod3 n)  ∨ (mod5 n))




record MultipleOf3Or5 : Set where
  constructor mul
  field
    number : ℕ
    proof : isMultipleOf3Or5 number

isMultipleOf3Or5isProp : (n : ℕ) → isProp (isMultipleOf3Or5 n)
isMultipleOf3Or5isProp n q1 q2 with ((mod3 n)  ∨ (mod5 n))
...| true  = refl
...| false   = ⊥-elim q1


MultipleOf3Or5-inj : isInj MultipleOf3Or5.number
MultipleOf3Or5-inj  (mul number proof) (mul .number proof₁) refl = cong (mul number) ((isMultipleOf3Or5isProp number) proof proof₁)
