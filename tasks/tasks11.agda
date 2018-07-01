{-# OPTIONS --without-K #-}

module tasks11 where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_)
open import Data.Unit
open import lect11

-- 1. Докажите, что (n + m)-элементное множество равно размеченному объединению n- и m-элементного.
finto : (n m : ℕ) → Fin (n + m) → Fin n ⊎ Fin m
finto  zero _ p = inj₂ p
finto  (suc n) _ zero  = inj₁ zero
finto  (suc n) m (suc h) with (finto n m h)
... | inj₁ x = inj₁ (suc x)
... | inj₂ x  = inj₂ x

finfrom : (n m : ℕ) → Fin n ⊎ Fin m → Fin (n + m)
finfrom zero _ (inj₁ ())
finfrom zero _ (inj₂ x) = x
finfrom (suc n) _ (inj₁ zero) = zero
finfrom (suc n) m (inj₁ (suc x)) = suc (finfrom n m (inj₁ x))
finfrom (suc n) m (inj₂ x) = suc (finfrom n m (inj₂ x))

finincto : (n m : ℕ ) -> (x : Fin (n + m)) →  (((finfrom (suc n) m) ((finto (suc n) m) (suc x))) ≡ (suc ((finfrom n m) ((finto n m) x))))
finincto zero _ p = refl
finincto (suc n) _ zero = refl
finincto (suc n) m (suc h) with (finto n m h)
... | inj₁ x = refl
... | inj₂ x = refl


fincastr : (n m : ℕ) → (x : Fin (n + m)) → ((finfrom n m) ((finto n m) x) ≡ x)
fincastr zero _ p = refl
fincastr (suc n) _ zero = refl
fincastr (suc n) m (suc l) = trans (finincto n m l) (cong suc (fincastr n m l))


infstep : (n m : ℕ) → Fin n ⊎ Fin m → Fin (suc n) ⊎ Fin m
infstep _ _ (inj₁ x) = inj₁ (suc x)
infstep _ _ (inj₂ y) = inj₂ y

incfrominj1 : (n m : ℕ ) -> (h : Fin n) → ( (finto (suc n) m (suc (finfrom n m (inj₁ h)))) ≡  ((infstep n m (finto n m (finfrom n m (inj₁ h))))))
incfrominj1 n m h with  (finto n m (finfrom n m (inj₁ h)))
... | inj₁ x = refl
... | inj₂ x = refl

incfrominj2 : (n m : ℕ ) -> (h : Fin m) → ( (finto (suc n) m (suc (finfrom n m (inj₂ h)))) ≡  ((infstep n m (finto n m (finfrom n m (inj₂ h))))))
incfrominj2 n m h with  (finto n m (finfrom n m (inj₂ h)))
... | inj₁ x = refl
... | inj₂ x = refl

fincastl : (n m : ℕ) → (y : Fin n ⊎ Fin m) → ((finto n m) ((finfrom n m) y) ≡ y)
fincastl zero _ (inj₁ ())
fincastl zero _ (inj₂ x) = refl
fincastl (suc _) _ (inj₁ zero) = refl
fincastl (suc n) m (inj₁ (suc h)) = trans (incfrominj1 n m h) (cong (infstep n m) (fincastl n m (inj₁ h)))
fincastl (suc n) m (inj₂ h) =  trans (incfrominj2 n m h) (cong (infstep n m) (fincastl n m (inj₂ h)))

Fin-sum : (n m : ℕ) → Fin (n + m) ≡ (Fin n ⊎ Fin m)
Fin-sum n m = SetExt ( to , fromproof )
  where
    to  = finto n m
    from : Fin n ⊎ Fin m → Fin (n + m)
    from = finfrom n m 
    proof : ((x : Fin (n + m)) → from (to x) ≡ x) × ((y : Fin n ⊎ Fin m) → to (from y) ≡ y)
    proof = ((fincastr n m) , (fincastl n m))
    fromproof : isBij to
    fromproof = ( from , proof )

-- 2. Докажите, что тип равенств между множествами хоть и не является утверждением, но является множеством.

Set-isGpd : (A B : Set) → isSet (A ≡ B)
Set-isGpd A B x y = {!!}

-- 3. Докажите, что аксиома K не выполняется для множеств.

K : ∀ {l} → Set l → Set l
K A = (a : A) (p : a ≡ a) → p ≡ refl

b1 : Bool ≡ Bool
b1 = refl
b2 : Bool ≡ Bool
b2 = SetExt (not , not , not-not , not-not)

b1≡b2 : K Set → b1 ≡ b2
b1≡b2 p = (trans (p Bool refl) (sym (p Bool b2)))

idb : Bool → Bool
idb b = b

idb≡not : b1 ≡ b2 → idb ≡ not
idb≡not p =  (cong proj₁ (trans (cong ≡-Bij p) (proj₂ (proj₂ SetUni) (not , not , not-not , not-not))))

true≡false :  idb ≡ not → true ≡ false
true≡false p =  funExtInv (λ x → x) not p true


K-is-false : K Set → ⊥
K-is-false p  = subst  T (true≡false (idb≡not (b1≡b2 p))) tt
   

-- 4. Докажите, что inv является обратным к **.

inv-left : {A : Set} {x y : A} (p : x ≡ y) → inv p ** p ≡ idp
inv-left refl = refl

inv-right : {A : Set} {x y : A} (p : x ≡ y) → p ** inv p ≡ idp
inv-right refl = refl

-- 5. Для любого группоида A постройте группу автоморфизмов его элемента a : A.

record Group (A : Set) : Set where
  constructor group
  field
    set : isSet A
    id : A
    _&_ : A → A → A
    ginv : A → A
    assoc : {x y z : A} → (x & y) & z ≡ x & (y & z)
    id-left : {x : A} → id & x ≡ x
    id-right : {x : A} → x & id ≡ x
    ginv-left : {x : A} → ginv x & x ≡ id
    ginv-right : {x : A} → x & ginv x ≡ id

aut : {A : Set} → isGpd A → (a : A) → Group (a ≡ a)
aut {A} gp a = record
            { set = gp a a ; id-left = λ {x} → idp-left x 
            ; id-right = λ {x} → idp-right x  ; ginv-left = λ {x} → inv-left x
            ; assoc = λ {x} {y} {z} → **-assoc x y z  ; ginv-right = λ {x} → inv-right x
             ; id = idp   ; _&_ = _**_  ; ginv = inv
            }

-- 6. Докажите, что множество автоморфизмов 2-х элементного множества состоит из двух элементов.

data Bool₁ : Set₁ where
  true false : Bool₁


record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

-- Default proof
isSet-lem : {A : Set} (R : A → A → hProp) →
  ({x y : A} → x ≡ y → hProp.A (R x y)) →
  ({x y : A} → hProp.A (R x y) → x ≡ y) →
  isSet A
isSet-lem {A} R f g x y p q = trans (sym (lem₁ p)) (trans (cong g (hProp.proof (R x y) _ _)) (lem₁ q))
  where
    h : {x y : A} → x ≡ y → x ≡ y
    h p = g (f p)

    cancel-right : {A : Set} {x y : A} (p : x ≡ x) (q : x ≡ y) →
                   p ** q ≡ q → p ≡ idp
    cancel-right p refl t = t

    h-idemp : {x y : A} (p : x ≡ y) → h (h p) ≡ h p
    h-idemp {x} {y} p = cong g (hProp.proof (R x y) _ _)

    lem₂ : (h : {x y : A} → x ≡ y → x ≡ y) {x y : A} (p : x ≡ y) →
           h p ≡ h idp ** p
    lem₂ h refl = refl

    lem₁ : {x y : A} (p : x ≡ y) → h p ≡ p
    lem₁ refl = cancel-right (h refl) (h refl) (trans (sym (lem₂ h (h idp))) (h-idemp idp))


bi1 : Bij Bool Bool
bi1 = (λ x → x) , (λ x → x) , (λ x → refl),  (λ x → refl)
bi2 : Bij Bool Bool
bi2 = (not , not , not-not , not-not)

elem1 : (Bool ≡ Bool)
elem1 =  (SetExt bi1)

elem2 : (Bool ≡ Bool)
elem2 = (SetExt bi2)

notp1 : elem1 ≡ elem2 → ⊥
notp1 e =
  let is1 = (proj₂ (proj₂ SetUni) bi2) in
  let is2 = (proj₂ (proj₂ SetUni) bi1) in
  let arg = trans (sym is2) (trans (cong ≡-Bij e) is1) in
  subst T (cong (λ x → proj₁ x true) arg) tt

exists : {A : Set} → (x : A) → Σ A (λ y → x ≡ y)
exists x = x , refl



⊤-isProp : isProp ⊤
⊤-isProp _ _ = refl


isSet-Bool : isSet Bool
isSet-Bool = isSet-lem (λ x y → prop (A x y) (proof x y)) R L where
  A : Bool → Bool → Set
  A x y  =  if (x xor y) then  ⊥ else  ⊤
  proof : (x y  : Bool) → isProp (A x  y)
  proof false false = ⊤-isProp
  proof false true = λ x → λ ()
  proof true false = λ x → λ ()
  proof true true = ⊤-isProp
  L : {x y : Bool} → A x  y → x ≡ y
  L  {false} {false} p = refl
  L  {false} {true} ()
  L {true} {false} ()
  L {true} {true} p = refl
  R : {x y : Bool} → x ≡ y → A x  y
  R {false} {.false} refl = tt
  R {true} {.true} refl = tt


proof : (x y : Σ (Bool → Bool) (λ f → Σ (Bool → Bool) (λ g → (((x : Bool) → g (f x) ≡ x) × ((y : Bool) → f (g y) ≡ y))))) → proj₁ x ≡ proj₁ y → proj₁ (proj₂ x) ≡ proj₁ (proj₂ y) → x ≡ y
proof (a , b , c , _) (.a , .b , g , _) refl refl with funExt c g (λ x → isSet-Bool (b (a x)) x (c x) (g x))
proof (a , b , c , d) (.a , .b , .c , h) refl refl | refl with funExt d h λ x → isSet-Bool (a (b x)) x (d x) (h x)
proof (a , b , c , d) (.a , .b , .c , .d) refl refl | refl | refl = refl

is2se : (e : Bool ≡ Bool) → elem1  ≡ e ⊎ elem2 ≡ e
is2se  e with exists (proj₁ (≡-Bij e) true)


is2se  e | true , b = inj₁ (trans (cong SetExt beq1) ((proj₁ (proj₂ SetUni)) e)) where
    beq1 : bi1 ≡ ≡-Bij e
    beq1 with exists (≡-fun e false)
    ... | false , c with funExt (λ x → x) (≡-fun e) (λ { true → sym b ; false → sym c })
    ... | _ with exists ((proj₁ (≡-fun-isBij e)) true)
    ... | false , l with exists (≡-Bij e)
    ... | ( _ , f , d , _) , m with trans (trans (sym l) (cong (λ x → proj₁ (proj₂ x) true) m)) (trans (cong f (trans (sym b) (cong (λ x → proj₁ x true) m))) (d true))
    ... | ()
    beq1 | false , c | ff | true , l with exists ((proj₁ (≡-fun-isBij e)) false)
    ... | false , m with funExt (λ x → x) (proj₁ (≡-fun-isBij e)) ((λ { true → sym l ; false → sym m }))
    ... | ss = proof ((λ x → x) , (λ x → x) , (λ x → refl) , (λ x → refl)) (≡-fun e , ≡-fun-isBij e) ff ss
    beq1 | false , c | ff | true , l | true , m with exists (≡-Bij e)
    ... | (_ , f , d , _) , n with trans (trans (sym m) (cong (λ x → proj₁ (proj₂ x) false) n)) (trans (cong f (trans (sym c) (cong (λ x → proj₁ x false) n))) (d false))
    ... | ()
    beq1 | true , c with exists (≡-Bij e)
    ... | (aa , f , _ , ee) , l with exists (f false)
    ... | false , m with trans (trans (trans (sym c) (cong (λ x → proj₁ x false) l)) (sym (cong aa m))) (ee false)
    ... | ()
    beq1 | true , c | (aa , _ , _ , ee) , l | true , m with trans (trans (trans (sym b) (cong (λ x → proj₁ x true) l)) (sym (cong aa m))) (ee false)
    ... | ()



is2se  e | false , b = inj₂ (trans (cong SetExt beq2) ((proj₁ (proj₂ SetUni)) e)) where
    beq2 : bi2 ≡ ≡-Bij e
    beq2 with exists (≡-fun e false)
    beq2 | true , c with
                funExt not (≡-fun e) (λ { true → sym b ;
                                          false → sym c })
    ...  | _ with
                 exists ((proj₁ (≡-fun-isBij e)) true)
    ...  | false , l with
                 exists ((proj₁ (≡-fun-isBij e)) false)
    ...  | false , m with exists (≡-Bij e)
    ...  | (_ , f , d , _) , n with
                trans (trans (trans (sym m) (cong (λ x → proj₁ (proj₂ x) false) n)) (cong f (trans (sym b) (cong (λ x → proj₁ x true) n)))) (d true)
    ...  | ()
    beq2 | true , c | ff | false , l | true , m with
                funExt not (proj₁ (≡-fun-isBij e)) ((λ { true → sym l ; false → sym m }))
    ... | ss = proof bi2 (≡-fun e , ≡-fun-isBij e) ff ss
    beq2 | true , c | _ | true , l with
                exists (≡-Bij e)
    ... | (aa , _ , _ , ee) , n  with
                trans (sym (trans (sym (cong (λ x → proj₁ x true) n)) b)) (trans (cong aa (trans (sym l) (cong (λ x → proj₁ (proj₂ x) true) n))) (ee true))
    ... | ()
    beq2 | false , c with
                  exists (≡-Bij e)
    beq2 | false , c | (aa , w , _ , ee) , l with
                   exists (w true)
    ...   | false , m with
                  trans (sym c) (trans (cong (λ x → (proj₁ x) false) l) (trans (sym (cong aa m)) (ee true)))
    ...   | ()
    beq2 | false , c | (aa , _ , _ , ee) , l | true , m
                   with trans (sym b) (trans (cong (λ x → (proj₁ x) true) l) (trans (sym (cong aa m)) (ee true))) 
    ...   | ()

 
2elmt : (A B : Set₁) → (x a : A) →
                     (y b : B) →
                     ((x ≡ a) → ⊥) →
                     ((y ≡ b) → ⊥) → 
                     ((e : A) → x ≡ e ⊎ a ≡ e) →
                     ((e : B) → y ≡ e ⊎ b ≡ e) → A ≡ B
2elmt A B x a y b p q f g = SetExt (to , rev , z , r) where
  rev : B → A
  rev b with g b
  ... | inj₁ y = x
  ... | inj₂ y = a
  to : A → B
  to a with f a
  ... | inj₁ x = y
  ... | inj₂ x = b
  r : (y₁ : B) → to (rev y₁) ≡ y₁
  r  e with g e
  r e | inj₂ y with f a
  ... | inj₁ x with p x
  ... | ()
  r e | inj₂ y | inj₂ _ = y
  r e | inj₁ y with f x
  ... | inj₁ x = y
  ... | inj₂ y₂ with p (sym y₂)
  ... | ()
  z : (x₁ : A) → rev (to x₁) ≡ x₁
  z e with f e
  z e | inj₂ y with g b
  ... | inj₁ x with q x
  ... | ()
  z e | inj₂ y | inj₂ _ = y
  z e | inj₁ x with g y
  ... | inj₁ _  = x
  z _ | inj₁ refl | inj₂ y with q (sym y)
  ... |  ()

aut-Bool : (Bool ≡ Bool) ≡ Bool₁
aut-Bool = 2elmt (Bool ≡ Bool) Bool₁ elem1 elem2 true false notp1 (λ ()) is2se λ {true → inj₁ refl; false → inj₂ refl}

-- 7. Докажите, что группа автоморфизмов в общем случае не коммутативна.


_**'_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p **' refl = p


aut-is-not-comm : ((A : Set) (p q : A ≡ A) → p **' q ≡ q **' p) → ⊥
aut-is-not-comm f = {!!}


-- 8. Докажите, что isProp является предикатом.

isProp-isProp : {A : Set} → isProp (isProp A)
isProp-isProp = {!!}
