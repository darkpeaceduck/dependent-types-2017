module lect06 where

open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_<_; Ordering; compare)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.List hiding (filter; _++_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Vec
open import Data.Product

-- 1. with

-- filter через with
filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true = x ∷ filter p xs
... | false = filter p xs

foo'''' : (x : ℕ) → x ≡ 0
foo'''' = {!!}

bar'''' : (x : ℕ) → x ≡ 0
bar'''' x with foo'''' x
bar'''' .0 | refl = refl

-- filter через helper
filter' : {A : Set} → (A → Bool) → List A → List A
filter' p [] = []
filter' {A} p (x ∷ xs) = helper (p x) (filter' p xs)
  where
    helper : Bool → List A → List A
    helper true ys = x ∷ ys
    helper false ys = ys

-- 2. case в языках с зависимыми типами.

-- через with
foo : {A : Set} (p : A → Bool) (a : A) → p a ≡ not (not (p a))
foo p a with p a
... | true = refl
... | false = refl

-- через helper
foo' : {A : Set} (p : A → Bool) (a : A) → p a ≡ not (not (p a))
foo' p a = helper (p a)
  where
    helper : (x : Bool) → x ≡ not (not x)
    helper true = refl
    helper false = refl

-- через with
bar : {A : Set} (p q : A → Bool) (a : A) → q a ≡ not (p a) → not (q a) ≡ p a
bar p q a r with p a
... | true = cong not r
... | false = cong not r

_<=_ : ℕ → ℕ → Set
_<=_ = {!!}

<=-refl : (n : ℕ) → n <= n
<=-refl = {!!}

<=-cong : (n m : ℕ) → n <= m → suc n <= suc m
<=-cong = {!!}

<=-suc : (n m : ℕ) → n <= m → n <= suc m
<=-suc = {!!}

filter-lem : {A : Set} (p : A → Bool) (xs : List A)
  → length (filter p xs) <= length xs
filter-lem p [] = <=-refl 0
filter-lem p (x ∷ xs) with p x
... | true = <=-cong (length (filter p xs)) (length xs) (filter-lem p xs)
... | false = <=-suc (length (filter p xs)) (length xs) (filter-lem p xs)

-- filter p (x ∷ xs) = case p x of { ... }

-- length (case p x of { ... }) ≤ length (x ∷ xs)

-- 3. Одновременная абстракция.

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc x < suc y = x < y

data Ordering : Set where
  LT GT EQ : Ordering

-- последовательный with
compare : ℕ → ℕ → Ordering
compare x y with x < y
... | false with y < x
... | true = GT
... | false = EQ
compare x y | true = LT

-- параллельный with
compare' : ℕ → ℕ → Ordering
compare' x y with x < y | y < x
compare' x y | false | false = EQ
compare' x y | false | true = GT
compare' x y | true | _ = LT

-- 4. rewrite

-- через subst
rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev [] = []
rev {A} (_∷_ {n} x xs) = subst (Vec A) (+-comm n 1) (rev xs ++ (x ∷ []))

-- через with
rev' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev' [] = []
rev' (_∷_ {n} x xs) with suc n | +-comm n 1
rev' (_∷_ {n} x xs) | .(n + 1) | refl = rev' xs ++ (x ∷ [])

rev'''' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev'''' [] = []
rev'''' (_∷_ {n} x xs) with n + 1 | +-comm n 1 | rev'''' xs ++ (x ∷ [])
rev'''' (_∷_ {n} x xs) | .(suc n) | refl | r = r

-- через helper
rev'' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev'' [] = []
rev'' {A} (_∷_ {n} x xs) =
      helper (n + 1) (+-comm n 1) (rev'''' xs ++ (x ∷ []))
  where
    helper : (k : ℕ) (p : k ≡ suc n) (ys : Vec A k) → Vec A (suc n)
    helper .(suc n) refl r = r

-- через rewrite
rev''' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev''' [] = []
rev''' (_∷_ {n} x xs) rewrite +-comm 1 n = rev''' xs ++ (x ∷ [])

-- 5. Views.

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

div2 : ℕ → ℕ
div2 n with parity n
div2 (.(k * 2)) | even k = k
div2 (.(suc (k * 2))) | odd k = k

-- 6. Разрешимые равенства и предикаты.

Pred : Set → Set₁
Pred A = (A → Set)

DecPred : Set → Set
DecPred A = (A → Bool)

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : (P → ⊥) → Dec P

-- Dec P

isDec : {A : Set} (P : A → Set) → Set
isDec {A} P = (a : A) → Dec (P a)

-- A → Set
-- A → Bool

-- p : ℕ → Set
-- p n = "машина Тьюринга с номером n останавливается на входе 0"

isEven : ℕ → Set
isEven n = Σ ℕ (λ k → n ≡ k * 2)

-- isEven-Dec : isDec isEven
-- isEven-Dec n with parity n
-- ... | even k = yes (k , refl)
-- ... | odd k = no (λ p → par-lem k (proj₁ p) (proj₂ p))
--   where
--     par-lem : (n k : ℕ) → suc (n * 2) ≡ k * 2 → ⊥
--     par-lem zero zero ()
--     par-lem zero (suc k₁) ()
--     par-lem (suc n) zero ()
--     par-lem (suc n) (suc k₁) p = par-lem n k₁ (cong pred (cong pred p))

ℕ-Dec : (x y : ℕ) → Dec (x ≡ y)
ℕ-Dec zero zero = yes refl
ℕ-Dec zero (suc y) = no (λ ())
ℕ-Dec (suc x) zero = no (λ ())
ℕ-Dec (suc x) (suc y) with ℕ-Dec x y
... | yes p = yes (cong suc p)
... | no f = no (λ q → f (cong pred q))

-- 7. Эквивалентность предикатов A -> Bool и разрешимых предикатов.

P-DP : {A : Set} (P : A → Set) → isDec P → A → Bool
P-DP P d a with d a
... | yes _ = true
... | no _ = false

DP-P : {A : Set} → (A → Bool) → A → Set
DP-P p a = T (p a)

DP-Dec : {A : Set} (P : A → Bool) → isDec (DP-P P)
DP-Dec P a with P a
... | true = yes tt
... | false = no (λ ())

DP-P-DP : {A : Set} (P : A → Bool) →
  (a : A) → P-DP (DP-P P) (DP-Dec P) a ≡ P a
DP-P-DP P a with DP-Dec P a
DP-P-DP P a | yes x with P a
... | true = refl
DP-P-DP P a | yes () | false
DP-P-DP P a | no x with P a
... | true = ⊥-elim (x tt)
... | false = refl

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

P-DP-P : {A : Set} (P : A → Set) (d : isDec P) (a : A) → DP-P (P-DP P d) a ↔ P a
P-DP-P {A} P d a = fun₁ , fun₂
  where
    fun₁ : DP-P (P-DP P d) a → P a
    fun₁ e with d a
    fun₁ e | yes x = x
    fun₁ () | no x

    fun₂ : P a → DP-P (P-DP P d) a
    fun₂ e with d a
    fun₂ e | yes x = tt
    fun₂ e | no x = x e
