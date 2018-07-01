module tasks05 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Char
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive  renaming (_⊔_ to _⊔l_)

-- 1. Определите запись Point, который может хранить элементы произвольных типов A и B произвольных уровней.
--    Определите равенство для такого типа Point.
record Point {l} {r} (A : Set l) (B : Set r) : Set (l ⊔l r) where
  constructor point
  field
    x : A
    y : B

_==P_ :  {l r : Level} {A : Set l} {B : Set r} →  (_==A_ : A →  A → Bool) -> (_==B_ : B → B → Bool) → Point A B → Point A B → Bool
_==P_ cpmf cpms (point a b) (point a' b') = (cpmf a a') ∧ (cpms b b')

-- 2. Используя тип List, определите тип данных (через зависимые записи) списков длины n (число должно быть параметром записи).


-- 3. Определите тип (через зависимые записи) четных натуральных чисел.
--    Определите функцию деления на 2.

isEven : ℕ → Bool
isEven zero = true
isEven (suc x) = not (isEven x)

record Evenℕ : Set where
  constructor even
  field
     v : ℕ
     proof : T (isEven v)

div2 : Evenℕ → ℕ
div2 record { v = x; proof = tt} = ⌈ x /2⌉


-- 4. Постройте структуру моноида на типе натуральных чисел (т.е. нужно сконструировать элемент соответствующей записи).

record Monoid : Set₁ where
  field
    A : Set
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

ℕ-Monoid : Monoid
ℕ-Monoid = record
            { A = ℕ
             ; id = 0
             ; _#_ = _+_
             ; assoc = assoc
             ; id-left = λ a → refl
             ; id-right =  id-right
            }
         where
           id-right : (x : ℕ) → (x + 0 ≡ x)
           id-right zero = refl
           id-right (suc x) = cong suc (id-right x)

           assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
           assoc zero    _ _ = refl
           assoc (suc m) n o = cong suc (assoc m n o)

-- 5. Напишите тип монады (через зависимые записи).
--    Элементы этого типа должны удовлетворять всем законом монад.

record Monad (M : Set → Set) : Set₁ where
  field
    return : {B : Set} (A : B)  → M B
    _>>=_ : {A B : Set} → (M A) → (A → M B) → M B

    pr1 : {A : Set} {B : Set} (f : A → M B) (a : A)  → (((return a) >>= f)  ≡ (f a))
    pr2 : {A : Set} {m : M A} → (( _>>=_  m return) ≡ m)
    pr3 : {A B C : Set} (m : M A) {f : A → M B} {g : B → M C} →  (((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g)))  
   
    

-- 6. Определите тип данных Maybe, сконструируйте структуру функтора и монады на этом типе.

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) → fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

Maybe-Functor : Functor Maybe
Maybe-Functor = record
  { fmap  = mfmap
   ; fmap-id = mfmap-id
   ; fmap-comp = mfmap-comp
   }  where
   mfmap : {A B : Set} → (A → B) → (Maybe A) → (Maybe B)
   mfmap f (just a) = just (f a)
   mfmap f nothing = nothing

   mfmap-id : {A : Set} (a : Maybe A) →  mfmap (λ x → x) a ≡ a
   mfmap-id nothing = refl
   mfmap-id (just a) = refl
   mfmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : Maybe A) → (mfmap (λ x → g (f x)) a ≡ mfmap g (mfmap f a))
   mfmap-comp f g nothing = refl
   mfmap-comp f g (just a) = refl


Maybe-Monad : Monad Maybe
Maybe-Monad = record
  {  return = mreturn
    ; _>>=_ = _mnext_
    ; pr1 = (λ x y → refl)
    ; pr2 = mpr2
    ; pr3 = mpr3
    } where
    mreturn : {B : Set} (A : B)  → Maybe B
    mreturn x = just x
    _mnext_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
    _mnext_ (just a) f = f a
    _mnext_ nothing f = nothing
    mpr2 : {A : Set} {m : Maybe A} → (( _mnext_  m mreturn) ≡ m)
    mpr2 {m = nothing} = refl
    mpr2 {m = just a} = refl
    mpr3 : {A B C : Set} (m : Maybe A) {f : A → Maybe B} {g : B → Maybe C}  →  (((m mnext f) mnext g) ≡ (m mnext (λ (x : A) → (f x) mnext g)))
    mpr3 nothing  = refl
    mpr3 (just a)  = refl
    
   

-- 7. Определите тип данных State, сконструируйте структуру функтора и монады на этом типе.
data State (S : Set) (A : Set) : Set where
  state :  (S → Point A S) → State S A

runState : {S : Set} {A : Set} → (State S A) → (S → Point A S)
runState (state f) = f

State-Monad : {S : Set} → Monad (State S) 
State-Monad {S} = record
  {  return = mreturn
    ; _>>=_ = _mnext_
    ; pr1 = mpr1
    ; pr2 = mpr2
    ; pr3 = mpr3
    } where
    mreturn : {B : Set} (A : B) → State S B
    mreturn a = state (λ s → point a s)
    _mnext_ : {A B : Set} → (State S A) → (A → State S B) → (State S B)
    st mnext f = state (λ s → let q = (runState st s) in  ( (runState (f (Point.x q)) (Point.y q))))
    mpr1 : {A : Set} {B : Set} (f : A → State S B) (a : A)  → (((mreturn a) mnext f)  ≡ (f a))
    mpr1 f a = aga (f a) where
      aga : {B : Set} → (st : State S B) → (state (runState st) ≡ st)
      aga (state f) = refl
    mpr2 : {A : Set} {m : State S A} → (( _mnext_  m mreturn) ≡ m)
    mpr2 {m = state f} = refl
    mpr3 : {A B C : Set} (m : State S A) {f : A → State S B} {g : B → State S C}  →  (((m mnext f) mnext g) ≡ (m mnext (λ (x : A) → (f x) mnext g)))
    mpr3 (state f) = refl




State-Functor : {S : Set} → Functor (State S)
State-Functor {s} = record
  { fmap  = mfmap
   ; fmap-id = mfmap-id
   ; fmap-comp =  mfmap-comp
   }  where
   mfmap : {A : Set} {B : Set}  → (A → B) → (State s A) → (State s B)
   mfmap f (state g)  = state (λ st → let p = g st in point (f (Point.x p)) (Point.y p) )
   mfmap-id : {A : Set} (a : State s A) →  mfmap (λ x → x) a ≡ a
   mfmap-id (state g) = refl
   mfmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : State s A) → (mfmap (λ x → g (f x)) a ≡ mfmap g (mfmap f a))
   mfmap-comp f g (state g') = refl


-- 8. Реализуйте sscanf.

data FmtData : Set where
    FmtNat FmtString : FmtData
    FmtChar : Char → FmtData

stringToFmtData : List Char → List FmtData
stringToFmtData ('%' ∷ 'd' ∷ xs) = FmtNat ∷ stringToFmtData xs
stringToFmtData ('%' ∷ 's' ∷ xs) = FmtString ∷ stringToFmtData xs
stringToFmtData (x ∷ xs) = FmtChar x ∷ stringToFmtData xs
stringToFmtData [] = []

Fmt : List FmtData → Set
Fmt (FmtNat ∷ xs) = ℕ → Fmt xs
Fmt (FmtString ∷ xs) = List Char → Fmt xs
Fmt (FmtChar x ∷ xs) = Fmt xs
Fmt [] = List Char

sscanf : (s : List Char) → (xs : List Char) → Fmt (stringToFmtData xs)
sscanf = {!!}
