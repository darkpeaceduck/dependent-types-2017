{-# OPTIONS --without-K #-}

module tasks09 where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.List hiding (filter)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Relation.Nullary
open import Data.Maybe.Base

-- 1. Мы будем говорить, что тип A тривиален, если существует элемент в A, такой что любой другой элемент в A равен ему.
--    Докажите, что тип A тривиален тогда и только тогда, когда A является утверждением и A населен.

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

isTriv : Set → Set
isTriv A = Σ A (λ x → (y : A) → x ≡ y)

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

p1-lem : (A : Set) → (x : A) → ((y : A) → (x ≡ y)) → ((x y : A) → x ≡ y)
p1-lem A x f x' y' = trans (sym (f x')) (f y')

p1 : (A : Set) → isTriv A → (isProp A × A)
p1 a ( x , prB ) = ( p1-lem a x prB , x)

p2 : (A : Set) → (isProp A × A) → isTriv A 
p2 a ( isPra , b) = (b , (isPra b))

isTriv-lem : (A : Set) → isTriv A ↔ (isProp A × A)
isTriv-lem A = ( (p1 A) , (p2 A) )

-- 2. Докажите, что T является утверждением.

T-isProp' : (x : Bool) → isProp (T x)
T-isProp' false a ()
T-isProp' true tt tt = refl

-- 3. Докажите, что ≤ является предикатом.

≤-isProp : {n m : ℕ} → isProp (n ≤ m)
≤-isProp (z≤n) (z≤n) = refl
≤-isProp  (s≤s  a) (s≤s  b) = cong s≤s (≤-isProp (a)  (b))

-- 4. Докажте, что следующий тип не является предикатом.

data _<='_ : ℕ → ℕ → Set where
  z<='n : {n : ℕ} → 0 <=' n
  foo : {n : ℕ} → n <=' n
  s<='s : {n m : ℕ} → n <=' m → suc n <=' suc m

lem : (z<='n ) ≡ (foo ) → ⊥
lem ()
≤=-notProp : ((n m : ℕ) → isProp (n <=' m)) → ⊥
≤=-notProp fprop = lem (fprop 0 0 (z<='n ) (foo ))
  
   

-- 5. Докажите, что если тип A вкладывается в тип B и B является утверждением, то и A является утверждением.

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

sub-isProp : {A B : Set} (f : A → B) → isInj f → isProp B → isProp A
sub-isProp f (inj) prB x y = inj x y (prB (f x) (f y))

-- 6. Докажите, что рекурсивно определенное равенство списков является предикатом.

record Prop : Set₁ where
  constructor prop'
  field
    A : Set
    prop : isProp A

eq : {A : Set} (_==_ : A → A → Prop) → List A → List A → Set
eq _ [] [] = ⊤
eq _ [] (_ ∷ _) = ⊥
eq _ (_ ∷ _) [] = ⊥
eq _==_ (x ∷ xs) (y ∷ ys) = Prop.A (x == y) × eq _==_ xs ys



eq-isProp : {A : Set} (_==_ : A → A → Prop) (xs ys : List A) → isProp (eq _==_ xs ys)
eq-isProp _==_ [] [] aexs bexs = refl
eq-isProp _==_ [] (x ∷ xs) ()
eq-isProp _==_ (x ∷ xs) [] ()
eq-isProp _==_ (x ∷ xs) (y ∷ ys) (ha , ta) (hb , tb) = cong₂ _,_ (lem3 _==_ x y ha hb) (eqr ta tb)
  where
    eqr = eq-isProp _==_ xs ys
    lem3 : {A : Set} (_==_ : A → A → Prop) → (x y : A) → (ha hb : Prop.A (x == y)) → ha ≡ hb
    lem3  _==_ x y ha hb = (Prop.prop (x == y)) ha hb

eq-Prop : {A : Set} (_==_ : A → A → Prop) → List A → List A → Prop
eq-Prop _==_ xs ys = record { A = eq _==_ xs ys ; prop = eq-isProp _==_ xs ys }

-- 7. Докажите, что Σ не является утверждением в общем случае.
fst : {A : Set} {B : A → Prop} → Σ A (λ x → Prop.A (B x)) → A
fst (a , _ ) = a

lem'' : {n m : ℕ} → (n <=' m) → Prop
lem'' _ = prop' (_≤_ 0 0) (≤-isProp) 

∃-isProp : ({A : Set} {B : A → Prop} → isProp (Σ A (λ x → Prop.A (B x)))) → ⊥
∃-isProp prop = lem (cong (fst {_<='_ 0 0} {lem''})  (prop {_<='_ 0 0} {lem''}  ( z<='n {0} , z≤n ) ( foo {0} , z≤n )))

-- 8. Докажите, используя функциональную экстенсиональность и лемму isSet-lem (саму лемму доказывать не нужно), что если для всех x : A верно, что B x является множеством, то (x : A) → B x также является множеством.

postulate
  funExt : {A : Set} {B : A → Set} (f g : (x : A) → B x)
           → ((x : A) → f x ≡ g x) → f ≡ g
isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

isSet-lem : {A : Set} (R : A → A → Prop) →
  ((x y : A) → x ≡ y → Prop.A (R x y)) →
  ((x y : A) → Prop.A (R x y) → x ≡ y) →
  isSet A
isSet-lem = {!!}


pppp'' : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) → (f g : (x : A) → B x) → (x : A) → isProp  (f x ≡ g x)
pppp'' h f g x = h x (f x) (g x)

∀-isProp' : {A : Set} {B : A → Set} → ((x : A) → isProp (B x))
            → isProp ((x : A) → B x)
∀-isProp' h f g = funExt f g (λ x → h x (f x) (g x))  

pppp : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) → (f g : (x : A) → B x) → isProp  ((x : A) → f x  ≡ g x)
pppp h f g = ∀-isProp'  (pppp'' h f g)


r : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) → (f g : (x : A) → B x) → Prop
r {A} h f g = prop' ((x : A) → f x ≡ g x) (pppp h f g)

r2 : {A : Set}  {B : A → Set} → (h : (x : A) → isSet (B x)) → (f g : (x : A) → B x) → f ≡ g → (Prop.A (r h f g))
r2 h f g eq x =  cong (λ f → f x) eq  

r3 : {A : Set}  {B : A → Set} → (h : (x : A) → isSet (B x)) → (f g : (x : A) → B x) → (Prop.A (r h f g)) → f ≡ g 
r3 h f g efxgx = funExt f g efxgx



Π-isSet : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) → isSet ((x : A) → (B x))
Π-isSet f = isSet-lem (r f) (r2 f) (r3 f)

-- 9. Докажите, используя лемму isSet-lem, что Σ сохраняет множества.
×-isProp : {A B : Set} → isProp A → isProp B → isProp (A × B)
×-isProp p q t s = cong₂ _,_ (p _ _) (q _ _)


Σ-isSet : {A : Set} {B : A → Set} → isSet A → ((x : A) → isSet (B x)) → isSet (Σ A B)
Σ-isSet = {!!}

-- 10. Докажите, используя лемму isSet-lem, что ⊎ сохраняет множества.
⊥-isProp : isProp ⊥
⊥-isProp x ()

a1 : {A B : Set} → isSet A → isSet B → (x y : A ⊎ B) → Prop
a1 _ _ (inj₁ x) (inj₂ y) = prop' ⊥ ⊥-isProp
a1 _ _ (inj₂ x) (inj₁ y) = prop' ⊥ ⊥-isProp
a1 pA _ (inj₁ x) (inj₁ y) = prop' (x ≡ y) (pA x y)
a1 _ pB (inj₂ x) (inj₂ y) = prop' (x ≡ y) (pB x y)

a2 : {A B : Set} → (ia : isSet A) → (ib : isSet B) → (x y : A ⊎ B) → x ≡ y → (Prop.A (a1 ia ib x y))
a2 _ _ (inj₁ x) (inj₂ y) ()
a2 _ _ (inj₂ x) (inj₁ y) ()
a2 pA _ (inj₁ x) .(inj₁ x) refl = refl 
a2 _ _ .(inj₂ y) (inj₂ y) refl = refl

a3 : {A B : Set} → (ia : isSet A) → (ib : isSet B) → (x y : A ⊎ B) → (Prop.A (a1 ia ib x y)) →  x ≡ y
a3 _ _ (inj₁ x) (inj₂ y) ()
a3 _ _ (inj₂ x) (inj₁ y) ()
a3 _ _ (inj₁ x) (inj₁ y) n = cong inj₁ n 
a3 _ _ (inj₂ x) (inj₂ y) n = cong inj₂ n

⊎-isSet : {A B : Set} → isSet A → isSet B → isSet (A ⊎ B)
⊎-isSet {A} {B} sA sB =  isSet-lem (a1 sA sB) (a2 sA sB) (a3 sA sB)

-- 11. Определите по аналогии с Prop тип типов, являющихся множествами.
record SSet : Set₁ where
  field
    A : Set
    prop : isSet A

-- 12. Докажите, используя лемму isSet-lem, что если равенство элементов типа A разрешимо, то A является множеством.

Hedberg : {A : Set} → ((x y : A) → Dec (x ≡ y)) → isSet A
Hedberg = {!!}
