{-# OPTIONS --without-K #-}

module tasks10 where

open import Data.Product renaming (∃ to exists)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Unit

open import Trunc

-- 1. Докажите следующие правила, характеризующие квантор существования.

∃ : (A : Set) (B : A → Set) → Set
∃ A B = ∥ Σ A B ∥

∃-intro : {A : Set} {B : A → Set} → (a : A) → B a → ∃[ x ∶ A ] (B x)
∃-intro a Ba = ∣ ( a , Ba ) ∣


∃-elim : {A : Set} {B : A → Set} {C : Set} → isProp C → ((a : A) → B a → C) → ∃ A B → C
∃-elim {A} {B} {C} isPrc abac eab = Trunc-rec isPrc f eab
  where
    f :  Σ A B → C
    f (a , b) = abac a b


syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B 


Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

-- 2. Определите утверждение "натуральные числа существуют".

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

isPropN : isProp  (∃[ x ∶ ℕ ] ⊤)
isPropN = trunc  

natural-numbers-exist : hProp
natural-numbers-exist = prop (∃[ x ∶ ℕ ] ⊤) isPropN

-- 3. Докажите, что функция pred сюръективна.

isSur : {A B : Set} → (A → B) → Set
isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

pred-is-sur : isSur pred
pred-is-sur x with x
...| 0 = ∣ ( 0 , refl ) ∣
...| (suc x') = ∣ ( (suc (suc x')) , refl ) ∣

-- 4. Докажите, что функция suc не сюръективна.

⊥-isProp : isProp ⊥
⊥-isProp x ()

suc-is-not-sur : isSur suc → ⊥
suc-is-not-sur f = l1 (f 0)
  where 
    l2 : {x : ℕ} → (suc x ≡ 0) → ⊥
    l2 ()
    l3 :  Σ ℕ (λ x → suc x ≡ 0) → ⊥
    l3 (x , a) = l2 a
    l1 : ∃ ℕ (λ x → suc x ≡ 0)  → ⊥
    l1 a = Trunc-rec ⊥-isProp  l3 a 
-- 5. Пусть f : A → B и g : B → C ─ некоторые функции.
--    Докажите, что если f и g сюръективны, то g ∘ f также сюръективна.
--    Докажите, что если g ∘ f сюръективна, то g также сюръективна.

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

∃-isProp : {A : Set} {B : A → Set} → isProp (∃ A B)
∃-isProp = trunc

arge : {A B C : Set} → (f : A → B) → (g : B → C) → (x : A) → (y : B) →  (gfx : C) →  g y ≡ gfx →   f x ≡ y → g (f x) ≡ gfx
arge _ _ _ _ _ e1 e2 rewrite e2 = e1
    
∘-sur : {A B C : Set} (f : A → B) (g : B → C) → isSur f → isSur g → isSur (g ∘ f)
∘-sur {A} {B} {C} f g fs gs gfx = Trunc-rec ∃-isProp l1  (gs (gfx))
  where
    l2 :  (y : B) → g y ≡ gfx → Σ A  (λ x → f x ≡ y) → ∃[ x ∶ A ] ( g (f x) ≡ gfx)
    l2 y e1 (x , e2) rewrite e2 =  ∣ (x , arge f g x y gfx e1 e2) ∣
    l1 : Σ B  (λ y → g y ≡ gfx) → ∃[ x ∶ A ] ( g (f x) ≡ gfx)
    l1 (y , eq) = Trunc-rec ∃-isProp (l2 y eq) (fs y) 
    

∘-sur' : {A B C : Set} (f : A → B) (g : B → C) → isSur (g ∘ f) → isSur g
∘-sur' {A} {B} {C} f g isgf gfx = Trunc-rec ∃-isProp l1  (isgf (gfx))
  where
    l1 : Σ A  (λ x → g (f x) ≡ gfx) → ∃[ y ∶ B ] ( g y ≡ gfx)
    l1 (x , eq) = ∣ (f x , eq) ∣


-- 6. Докажите, что функция является биекцией тогда и только тогда, когда она является инъекцией и сюръекцией.

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

isBij : {A B : Set} → (A → B) → Set
isBij {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

isBij-isInj : {A B : Set} (f : A → B) → isBij f → isInj f
isBij-isInj  {A} {B} f isbi x y efxy =  l1 isbi
  where
    l4 : (g : B → A) → (g (f x) ≡ x) → g (f y) ≡ x
    l4 g e rewrite efxy = e
    l3 : (g : B → A) → (g (f y) ≡ x) → (g (f y) ≡ y) → (x ≡ y)
    l3 _ e1 e2 = trans (sym (e1)) e2
    l2 : (g : B → A) → (g (f x) ≡ x) → (g (f y) ≡ y) → (x ≡ y)
    l2 g e e2 = l3 g (l4 g e) e2  
    l1 :  Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y)) → (x ≡ y)
    l1 (g , (gr , fr) ) = l2 g (gr x) (gr y)
    

isBij-isSur : {A B : Set} (f : A → B) → isBij f → isSur f
isBij-isSur {A} {B} f isbi fx =  l1 isbi
  where
    l1 :  Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y)) → ∃[ x ∶ A ] ( f x ≡ fx)
    l1 (g , (gr , fr) ) = ∣ (g fx , fr fx) ∣ 

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

-- Эта лемма вам может пригодится
sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'}
  (p : a ≡ a') →
  subst B p b ≡ b' →
  _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl q = cong (_,_ _) q

isInj-isSur-isBij : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f → isBij f
isInj-isSur-isBij {A} {B} Bs f fi fs =
  (λ b → proj₁ (isInj-isSur-isBij' b)) ,
  (λ a → (fi (proj₁ (isInj-isSur-isBij' (f a))) a (proj₂ (isInj-isSur-isBij' (f a))))) , 
  (λ b → proj₂ (isInj-isSur-isBij' b))
  where
    l1 :  (y : B) → isProp  (Σ[ x ∶ A ](f x ≡ y)) 
    l1 y (x , efx) (x' , efx')  = let xeq = fi x x' (trans efx (sym efx')) in sigmaExt (xeq) (Bs (f x') (y) (subst (λ x₁ → f x₁ ≡ y) (xeq) efx) efx')
    isInj-isSur-isBij' : (y : B) → Σ[ x ∶ A ] (f x ≡ y)
    isInj-isSur-isBij' y = Trunc-rec (l1 y) (λ x → x) (fs y) 

    
-- 7. Докажите, что isBij является утверждением.

isBij-isProp : {A B : Set} → isSet A → isSet B → (f : A → B) → isProp (isBij f)
isBij-isProp = {!!}

-- 8. См. Cantor.agda.
