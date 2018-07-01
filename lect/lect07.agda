module lect07 where

open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_≤_; _<_; Ordering; compare)
open import Data.List hiding (zipWith)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum

-- 0. Коиндукция.

data Stream' (A : Set) : Set where
  cons : A → Stream' A → Stream' A

Stream'-isEmpty : {A : Set} → Stream' A → ⊥
Stream'-isEmpty (cons x xs) = Stream'-isEmpty xs

-- copatterns

record Point : Set where
  field
    getX : ℕ
    getY : ℕ

open Point

shift : Point → Point
shift p = record { getX = suc (getX p) ; getY = suc (getY p) }

shift' : Point → Point
getX (shift' p) = suc (getX p)
getY (shift' p) = suc (getY p)

-- coinductive record

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

repeat : {A : Set} → A → Stream A
head (repeat a) = a
tail (repeat a) = repeat a

stream-map : {A B : Set} → (A → B) → Stream A → Stream B
head (stream-map f xs) = f (head xs)
tail (stream-map f xs) = stream-map f (tail xs)

zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

fib : Stream ℕ
head fib = 0
head (tail fib) = 1
tail (tail fib) = zipWith _+_ fib (tail fib)

-- 1. Индуктивное определение предикатов.

_<='_ : ℕ → ℕ → Set
n <=' k = Σ ℕ (λ x → n + x ≡ k)

-- рекурсивно
_<=_ : ℕ → ℕ → Set
0 <= 0 = ⊤
suc x <= suc y = x <= y
_ <= _ = ⊥

data _==_ : ℕ → ℕ → Set where
  zz : 0 == 0
  ss : {n k : ℕ} → n == k → suc n == suc k

≡-== : {n k : ℕ} → n ≡ k → n == k
≡-== {0} refl = zz
≡-== {suc n} refl = ss (≡-== refl)

==-≡ : {n k : ℕ} → n == k → n ≡ k
==-≡ zz = refl
==-≡ (ss p) = cong suc (==-≡ p)

-- индуктивно
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → 0 ≤ n
  s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

-- индуктивно'
data _≤'_ : ℕ → ℕ → Set where
  ≤'-refl : {n : ℕ} → n ≤' n
  ≤'-step : {n m : ℕ} → n ≤' m → n ≤' suc m

z≤'n : {n : ℕ} → 0 ≤' n
z≤'n {zero} = ≤'-refl
z≤'n {suc n} = ≤'-step z≤'n

s≤'s : {n k : ℕ} → n ≤' k → suc n ≤' suc k
s≤'s ≤'-refl = ≤'-refl
s≤'s (≤'-step p) = ≤'-step (s≤'s p)

≤-≤' : {n k : ℕ} → n ≤ k → n ≤' k
≤-≤' z≤n = z≤'n
≤-≤' (s≤s p) = s≤'s (≤-≤' p)

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-step : {n k : ℕ} → n ≤ k → n ≤ suc k
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤'-≤ : {n k : ℕ} → n ≤' k → n ≤ k
≤'-≤ ≤'-refl = ≤-refl
≤'-≤ (≤'-step p) = ≤-step (≤'-≤ p)

-- 2. Предикат ``домен функции''

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc n < suc k = n < k

-- div'' : ℕ → ℕ → ℕ
-- div'' n k = if n < k then 0 else suc (div'' (n ∸ k) k)

data div-dom (n k : ℕ) : Set where
  lt : T (n < k) → div-dom n k
  geq : ¬ (T (n < k)) → div-dom (n ∸ k) k → div-dom n k

div' : {n k : ℕ} → div-dom n k → ℕ
div' (lt x) = 0
div' (geq x p) = suc (div' p)

div-dom-pos : (n k : ℕ) → div-dom n k → ¬ (k ≡ 0)
div-dom-pos n zero (lt ())
div-dom-pos n (suc k) (lt x) = λ ()
div-dom-pos n k (geq x p) = div-dom-pos (n ∸ k) k p

{-
div-dom-desc : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
div-dom-desc _ zero p = ⊥-elim (p refl)
div-dom-desc zero (suc k) p = lt tt
div-dom-desc (suc n) (suc k) p with div-dom-desc n k {!!}
div-dom-desc (suc n) (suc k) p | lt x = lt x
div-dom-desc (suc n) (suc k) p | geq x r = geq x {!!}
-}

{-
div-dom-desc : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
div-dom-desc _ zero p = ⊥-elim (p refl)
div-dom-desc zero (suc k) p = lt tt
div-dom-desc (suc n) (suc k) p with div-dom-desc n (suc k) p
div-dom-desc (suc n) (suc k) p | lt x = {!!}
div-dom-desc (suc n) (suc k) p | geq x r = geq {!!} {!!}
-}

{-
<-Dec : (n k : ℕ) → Dec (T (n < k))
<-Dec n k = {!!}

div-dom-desc : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
div-dom-desc n k p with <-Dec n k
div-dom-desc n k p₁ | yes p = lt p
div-dom-desc n k p | no ¬p = geq ¬p {!!}
-}

data ModView (m : ℕ) : ℕ → Set where
  quot-rem : ∀ q r → T (r < m) → ModView m (r + q * m)

mod-view : (m n : ℕ) → ¬ (m ≡ 0) → ModView m n
mod-view = {!!}

div-dom-desc : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
div-dom-desc n k p with mod-view k n p
div-dom-desc .(r + q * k) k p | quot-rem q r x = lem r q k x p
  where
    lem : (r q k : ℕ) → T (r < k) → ¬ (k ≡ 0) → div-dom (r + q * k) k
    lem r₁ zero k₁ p₁ t = lt {!!} -- легко
    lem r₁ (suc q₁) k₁ p₁ t = geq {!!} {!!}

-- 3. Принципы индукции.

{-
f : (x : ℕ) → P x
f 0 = ? : P 0
f (suc n) = ? : P n → P (suc n)
-}

ℕ-ind : (P : ℕ → Set) → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
ℕ-ind P z s zero = z
ℕ-ind P z s (suc n) = s n (ℕ-ind P z s n)

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

-- через ℕ-ind
fac' = ℕ-ind (λ _ → ℕ) 1 (λ n r → suc n * r)

ℕ-<-ind :
  (P : ℕ → Set) →
  ((n : ℕ) → ((k : ℕ) → T (k < n) → P k) → P n) →
  (n : ℕ) → P n
ℕ-<-ind P h n = {!!}

<-trans : (x y z : ℕ) → T (x < y) → T (y < z) → T (x < z)
<-trans zero zero zero () q
<-trans zero zero (suc z) () q
<-trans zero (suc y) zero p ()
<-trans zero (suc y) (suc z) p q = tt
<-trans (suc x) zero zero p ()
<-trans (suc x) zero (suc z) () q
<-trans (suc x) (suc y) zero p ()
<-trans (suc x) (suc y) (suc z) p q = <-trans x y z p q

<-step : (x : ℕ) → T (x < suc x)
<-step zero = tt
<-step (suc x) = <-step x

∸-lem' : (n k : ℕ) → T ((n ∸ k) < suc n)
∸-lem' zero zero = tt
∸-lem' zero (suc k) = tt
∸-lem' (suc n) zero = <-step n
∸-lem' (suc n) (suc k) = <-trans (n ∸ k) (suc n) (suc (suc n)) (∸-lem' n k) (<-step n)

∸-lem : (n k : ℕ) → ¬ k ≡ 0 → ¬ T (n < k) → T ((n ∸ k) < n)
∸-lem n k p q = {!!}
{-
∸-lem zero zero p q = p refl
∸-lem zero (suc k) p ()
∸-lem (suc n) zero p q = ⊥-elim (p refl)
∸-lem (suc n) (suc k) p q = ∸-lem' n k
-}

-- div'' : ℕ → ℕ → ℕ
-- div'' n k = if n < k then 0 else suc (div'' (n ∸ k) k)

-- через ℕ-<-ind
div : ℕ → (k : ℕ) → ¬ (k ≡ 0) → ℕ
div n k p = ℕ-<-ind (λ _ → ℕ) (λ n' r → lem n' {!!} r) n
  where
    lem : (n' : ℕ) → Dec (T (n' < k)) → ((n'' : ℕ) → T (n'' < n') → ℕ) → ℕ
    lem n' (yes p₁) r = 0
    lem n' (no ¬p) r = r (n' ∸ k) (∸-lem n' k p ¬p)
