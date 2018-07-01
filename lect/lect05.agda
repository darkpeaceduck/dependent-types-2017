module lect05 where

open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Relation.Binary.PropositionalEquality
-- open import Data.Product
open import Data.Sum
open import Data.Char
open import Data.List
open import Data.String hiding (_++_; _==_)

-- 1. Вселенные, полиморфизм по уровням.

-- A : Set -- A ─ тип
-- Set : Set
-- Set₀ ≡ Set0 ≡ Set
-- Set₀ : Set₁ : Set₂ : ...

fff : ∀ {l} → Set l → Set l
fff X = X

id'' : ∀ {l} {A : Set l} → A → A
id'' a = a

--- X : Set0 => X : Set1

ggg : Set₁₀₀ → ℕ
ggg X = let t = fff X in 0

-- f : Set₁₀₀₀₀₀₀₀₀₀₀₀ → Set₁₀₀₀₀₀₀₀₀₀₀₀
-- f X = X

data List' {l} (A : Set l) : Set l where
  nil : List' A
  cons : A → List' A → List' A

gg = cons ℕ (cons (ℕ → ℕ) nil)

g = ℕ → Set₀ → List Set₀ → List Set₁₀

h : ∀ {l} → Set l → Set l
h X = X

g' = h Set₁

-- 2. Records.

data Pair : Set where
  pair : ℕ → ℕ → Pair

fst : Pair → ℕ
fst (pair x _) = x

snd : Pair → ℕ
snd (pair _ y) = y

record Point : Set where
  constructor point
  field
    x : ℕ
    y : ℕ

somePoint : Point
somePoint = record { x = 13; y = 56 }

origin' = point 0 0

origin : Point
origin = record { x = 0; y = 0 }

{-
open Point

fst' : Point → ℕ
fst' = x
-}

_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' suc _ = false
suc _ ==' 0 = false
suc x ==' suc y = x ==' y

_==''_ : Point → Point → Bool
point x' y' =='' q =
  let open Point q in (x' ==' x) ∧ (y' ==' y)

data Point' : Set where
  point' : ℕ → ℕ → Point'

getX : Point' → ℕ
getX (point' x y) = x

getY : Point' → ℕ
getY (point' x y) = y

{-
_==''_ : Point' → Point' → Bool
point' x' y' =='' point' x y = x' =='' x && y' =='' y
-}

pfoo : (p : Point) → p ≡ record { x = Point.x p; y = Point.y p }
pfoo p = refl

qfoo : (p : Point') → p ≡ point' (getX p) (getY p)
qfoo p = {!!}

rfoo : (x y : ⊤) → x ≡ y
rfoo x y = refl

ffoo : getX ≡ (λ p → getX p)
ffoo = refl

-- Эта эквивалентность

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    a : A
    b : B a

-- Σ (x : A) B == Σ A (λ x → B)

foo : Σ ℕ (λ x → x ≡ 3)
foo = 3 , refl

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

bar : ℕ × ℕ
bar = 7 , 15

-- Σ (x : A) B == { x : A | B }

-- 3. Dependent records.

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

record Posℕ : Set where
  constructor posℕ
  field
    num : ℕ
    pos : T (isPos num)

-- open Posℕ

-- div : ℕ → Posℕ → ℕ
-- div n k = num k

{-
fooo : IO ℕ
fooo = do
  x <- readLn : IO ℕ
  if (x == 0) then ... else ...
  return (div 10 (poℕ x ?))
-}

-- 4. monoid

record Monoid : Set₁ where
  field
    A : Set
    
    e : A
    _#_ : A → A → A
    
    #-assoc : ∀ a a' a'' → ((a # a') # a'') ≡ (a # (a' # a''))
    e-idl : ∀ a → (e # a) ≡ a
    e-idr : ∀ a → (a # e) ≡ a

xor-Monoid : Monoid
xor-Monoid = record
             { A = Bool
             ; e = false
             ; _#_ = _xor_
             ; #-assoc = {!!}
             ; e-idl = λ a → refl
             ; e-idr = e-idr
             }
  where
    e-idr : (x : Bool) → x xor false ≡ x
    e-idr true = refl
    e-idr false = refl

-- 3. functor

record Functor (F : Set → Set) : Set1 where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (y : F A) → fmap (λ x → x) y ≡ y
    fmap-∘ : {A B C : Set} (f : A → B) (g : B → C) (a : F A) →
                fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

-- 4. sprintf

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

show' : ℕ → List Char
show' _ = 'x' ∷ []

sprintf' : List Char → (xs : List FmtData) → Fmt xs
sprintf' acc (FmtNat ∷ xs) = λ n → sprintf' (acc ++ show' n) xs
sprintf' acc (FmtString ∷ xs) = λ s → sprintf' (acc ++ s) xs
sprintf' acc (FmtChar x ∷ xs) = sprintf' (acc ++ (x ∷ [])) xs
sprintf' acc [] = acc

sprintf : (xs : List Char) → Fmt (stringToFmtData xs)
sprintf xs = sprintf' [] (stringToFmtData xs)

string : List Char
string = sprintf (primStringToList "abc%def%dgh") 37 56

string-isCorrect : string ≡ primStringToList "abcxefxgh"
string-isCorrect = refl
