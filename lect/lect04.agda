module lect04 where

open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding (subst; sym; trans; cong)

-- 1. Равенство в логике, равенство для различных типов.

infix 1 _==_
_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc x == suc y = x == y

eq : (ℕ → ℕ) → (ℕ → ℕ) → Set
eq f g = (x : ℕ) → T (f x == g x)

-- 2. Рефлексивность, симметричность, транзитивность, конгруэнтность, принцип Лейбница.

-- refl'' : (x : ℕ) → T (x == x)
-- sym'' : (x y : ℕ) → T (x == y) → T (y == x)
-- trans'' : (x y z : ℕ) → T (x == y) → T (y == z) → T (x == z)
-- cong'' : (f : ℕ → ℕ) (x y : ℕ) → T (x == y) → T (f x == f y)
-- subst'' : (P : ℕ → Set) (x y : ℕ) → T (x == y) → P x → P y

-- 3. Определение через индуктивные семейства.

{-
infix 1 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

infix 1 _≡'_
data _≡'_ {A : Set} : A → A → Set where
  refl' : {a : A} → a ≡' a
-}

-- 4. Симметричность, транзитивность и конгруэнтность через принцип Лейбница.

-- Принцип Лейбница
subst : {A : Set} (B : A → Set) {x y : A} → x ≡ y → B x → B y
subst _ refl b = b

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym {A} {x} {y} p = subst (λ a → a ≡ x) p refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {A} {x} {y} {z} p q = subst (_≡_ x) q p

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f {x} {y} p = subst (λ a → f x ≡ f a) p refl

-- 5. Пример доказательства.

+-assoc : (x y z : ℕ) → T ((x + y) + z == x + (y + z))
+-assoc zero y z = refl
+-assoc (suc x) y z = +-assoc x y z

+-assoc' : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc' zero y z = refl
+-assoc' (suc x) y z = cong suc (+-assoc' x y z)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm 0 y)
+-comm (suc x) zero = cong suc (+-comm x 0)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (+-comm y x)) (+-comm (suc x) y)))

open ≡-Reasoning

+-comm' : (x y : ℕ) → x + y ≡ y + x
+-comm' zero zero = refl
+-comm' zero (suc y) = cong suc (+-comm' zero y)
+-comm' (suc x) zero = cong suc (+-comm' x zero)
+-comm' (suc x) (suc y) = cong suc (
  begin
    x + suc y
  ≡⟨ +-comm x (suc y) ⟩
    suc (y + x)
  ≡⟨ cong suc (+-comm y x) ⟩
    suc (x + y)
  ≡⟨ +-comm (suc x) y ⟩
    y + suc x
  ∎)
rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev [] = []
rev {A} {suc n} (x ∷ xs) = subst (Vec A) (+-comm n 1) (rev xs ++ (x ∷ []))

++-assoc : {A : Set} {n m k : ℕ}
  (xs : Vec A n) (ys : Vec A m) (zs : Vec A k) →
  subst (Vec A) (+-assoc' n m k) ((xs ++ ys) ++ zs) ≡ xs ++ (ys ++ zs)
++-assoc {A} {.0} {m} {k} [] ys zs = refl
++-assoc {A} {suc n} {m} {k} (x ∷ xs) ys zs = trans (lemma (+-assoc' n m k) x ((xs ++ ys) ++ zs)) (cong (_∷_ x) (++-assoc xs ys zs))
  where
    lemma : {A : Set} {a b : ℕ} (p : a ≡ b) (x : A) (ws : Vec A a) →
            subst (Vec A) (cong suc p) (x ∷ ws) ≡ x ∷ subst (Vec A) p ws
    lemma refl x₁ ws = refl

-- 6. Доказательства неравенств.

0≠suc : (x : ℕ) → 0 ≡ suc x → ⊥
0≠suc x ()

D : ℕ → Set
D 0 = ⊤
D (suc x) = ⊥

0≠suc' : (x : ℕ) → 0 ≡ suc x → ⊥
0≠suc' x p = subst D p tt

==-≡ : (x y : ℕ) → T (x == y) → x ≡ y
==-≡ zero zero p = refl
==-≡ zero (suc y) ()
==-≡ (suc x) zero ()
==-≡ (suc x) (suc y) p = cong suc (==-≡ x y p)

≡-== : (x y : ℕ) → x ≡ y → T (x == y)
≡-== x .x refl = {!!}
