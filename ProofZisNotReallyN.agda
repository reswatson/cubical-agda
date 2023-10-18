
{-# OPTIONS --safe #-}
{-# OPTIONS --no-main #-}
{-# OPTIONS --cubical #-}

module ProofZisNotReallyN where

open import Cubical.Foundations.Prelude hiding (Σ-syntax)
open import Cubical.Foundations.Transport

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to Add)
open import Cubical.Data.Int
open import Data.Product.Base
open import Cubical.Relation.Nullary

-------------------------------------------

Addxy≡x≡0 : {x y : ℕ} → Add x y ≡ 0 → x ≡ 0
Addxy≡x≡0  add0 = proj₁ (m+n≡0→m≡0×n≡0 add0)

Addxy≡y≡0 : {x y : ℕ} → Add x y ≡ 0 → y ≡ 0
Addxy≡y≡0  add0 = proj₂ (m+n≡0→m≡0×n≡0 add0)

Addxx≡x≡0 : {x : ℕ} → Add x x ≡ x → x ≡ 0
Addxx≡x≡0 {x = x} = m+n≡n→m≡0

funExtApp-hlp :  {A B : Type} → {AB : A ≡ B} → (x : A) → PathP (λ i -> AB i) x (transport AB x)
funExtApp-hlp {A}{B}{AB} x = toPathP refl 
                        {- where
                             step1 : transport (λ i → AB i) x ≡ transport AB x
                             step1 = refl -}

funExtApp : {A B : Type} → {AB : A ≡ B}
  {f : A → A} {g : B → B}
  → PathP (λ i → AB i → AB i) f g
  → ((x : A) → PathP (λ i → AB i) (f x) (g (transport AB x)))
funExtApp {A}{B}{AB}{f}{g} pth x = λ i → pth i (funExtApp-hlp {A = A}{B = B}{AB = AB} x i)

funExtApp2 : {A B : Type} → {AB : A ≡ B}
  {f : A → A → A} {g : B → B → B}
  → PathP (λ i → AB i → AB i → AB i) f g
  → ((x : A) → PathP (λ i → AB i → AB i) (f x) (g (transport AB x)))
funExtApp2 {A} {B} {AB} {f} {g} pth x = λ i → pth i (funExtApp-hlp {A = A}{B = B}{AB = AB} x i)

transport-lemma : {A B : Type} → {AB : A ≡ B} → {f : A → A} → {g : B → B} → (tr : transport (λ i → AB i → AB i) f ≡ g) → ∀ x → transport AB (f x) ≡ g (transport AB x)  
transport-lemma {A} {B} {AB} {f} {g} tr x = fromPathP step1 
                                     where
                                       step2 : PathP (λ i → AB i → AB i) f g
                                       step2 = toPathP tr
                                       step1 : PathP (λ i → AB i) (f x) (g (transport (λ i → AB i) x))
                                       step1 = funExtApp step2 x

transport-lemma2 : {A B : Type} → {AB : A ≡ B} → {f : A → A → A} → {g : B → B → B} → transport (λ i → AB i → AB i → AB i) f ≡ g → ∀ x y → transport AB (f x y) ≡ g (transport AB x) (transport AB y)  
transport-lemma2 {A} {B} {AB} {f} {g} tr x y = fromPathP step1
                                       where
                                         BA : B ≡ A
                                         BA = sym AB
                                         step2 : PathP (λ i → AB i → AB i → AB i) f g
                                         step2 = toPathP tr
                                         step3 : PathP (λ i → AB i → AB i) (f x) (g (transport AB x))
                                         step3 = funExtApp2 (toPathP tr) x
                                         step1 : PathP (λ i → AB i) ((f x) y) (g (transport AB x) (transport AB y))
                                         step1 = funExtApp {f = f x} {g = g (transport AB x)} step3 y
 
--------------------------------------------

natsuc≠zero : {x : ℕ} → ¬ (ℕ.suc x ≡ ℕ.zero) 
natsuc≠zero {x = ℕ.zero} nn = snotz nn
natsuc≠zero {x = ℕ.suc x} nn = snotz nn

zero≢natsuc  : {x : ℕ} → ¬ (ℕ.zero ≡ ℕ.suc x)
zero≢natsuc {x = x} nn = znots nn

decℕ≡ : ∀ (p q : ℕ) → Dec (p ≡ q)
decℕ≡ ℕ.zero ℕ.zero =  yes refl
decℕ≡ ℕ.zero (ℕ.suc q) = no zero≢natsuc 
decℕ≡ (ℕ.suc p) ℕ.zero = no natsuc≠zero
decℕ≡ (ℕ.suc p) (ℕ.suc q) with (decℕ≡ p q)
...                        | yes pq = yes (cong (λ x → ℕ.suc x) pq)
...                        | no npq = no (λ x → npq (cong predℕ x))

decℕ≡' : ∀ {p q : ℕ} → Dec (p ≡ q)
decℕ≡' {p = p} {q = q} = decℕ≡ p q

natplusnat≠zero : {x y : ℕ} → Add (ℕ.suc x) (ℕ.suc y) ≡ ℕ.zero → ⊥
natplusnat≠zero {x = x} {y = y} addxy = natsuc≠zero addxy

DecoratedType : (Signature : ∀ (ty : Type) → Type) → Type₁
DecoratedType Signature = Σ Type Signature

Carrier : {Signature : ∀ (ty : Type) → Type} → (A : DecoratedType Signature) → Type
Carrier (fst₁ , snd₁) = fst₁

Sig :  {Signature : ∀ (ty : Type) → Type} → (A : DecoratedType Signature) → Signature (Carrier A)
Sig {Signature = Signature} (fst₁ , snd₁) = snd₁ 

BareNat : DecoratedType (λ ty → Unit)
BareNat = ℕ , tt

BareInt :  DecoratedType (λ ty → Unit)
BareInt = ℤ , tt

NatMagma* : DecoratedType (λ ty → (ty → ty → ty))  
NatMagma* =  ℕ , Add  

NatMagma : Σ[ ty ∈ Type ] (ty → ty → ty)
NatMagma =  ℕ , Add 

IntMagma* : DecoratedType (λ ty → (ty → ty → ty))
IntMagma* = ℤ , _+_

IntMagma : Σ[ ty ∈ Type ] (ty → ty → ty)
IntMagma = ℤ , _+_ 

ZNMagma+ : (INM : IntMagma ≡ NatMagma) → ∀ (x y : ℤ) → transport (cong fst INM) (x + y) ≡ Add (transport (cong fst INM) x) (transport (cong fst INM) y) 
ZNMagma+ INM x y  = transport-lemma2 {A = ℤ} {B = ℕ} {AB = cong fst INM} {f = _+_} {g = Add} tr' x y
                 where
                   pth : PathP (λ i → proj₁ (INM i) → proj₁ (INM i) → proj₁ (INM i))
                           (snd IntMagma) (snd NatMagma)
                   pth = cong (λ a -> snd a ) INM
                   tr' : transport (λ i → proj₁ (INM i) → proj₁ (INM i) → proj₁ (INM i)) (_+_) ≡ Add
                   tr' = fromPathP pth

0Is0-hlp2 : (INM : IntMagma ≡ NatMagma) → (x y : ℤ) → (x + y ≡ pos 0) → transport (cong fst INM) (x + y) ≡ transport (cong fst INM) (pos 0)
0Is0-hlp2 INM x y x+y = cong (λ x → transport (cong fst INM) x) x+y

0Is0-hlp3 : (INM : IntMagma ≡ NatMagma) → transport (cong fst INM) ((pos 0) + (pos 0)) ≡ transport (cong fst INM) (pos 0)
0Is0-hlp3 INM = 0Is0-hlp2 INM (pos 0) (pos 0) refl  

0Is0-hlp1 : (INM : IntMagma ≡ NatMagma) → Add (transport (cong fst INM) (pos 0)) (transport (cong fst INM) (pos 0)) ≡ transport (cong fst INM) (pos 0)
0Is0-hlp1 INM = (sym (ZNMagma+ INM (pos 0) (pos 0))) ∙ (0Is0-hlp2 INM (pos 0) (pos 0) refl) 

0Is0 : (INM : IntMagma ≡ NatMagma) → transport (cong fst INM) (pos 0) ≡ 0
0Is0 INM = m+n≡n→m≡0 (0Is0-hlp1 INM) 

1+-1Is0 : (INM : IntMagma ≡ NatMagma) → transport (cong fst INM) ((pos 1) + (negsuc 0)) ≡ 0
1+-1Is0 INM =  0Is0-hlp2 INM (pos 1) (negsuc 0) refl ∙ (0Is0 INM)

1Is0 : (INM : IntMagma ≡ NatMagma) → transport (cong fst INM) (pos 1) ≡ 0
1Is0 INM = Addxy≡x≡0 step3 
    where
      step1 : transport (cong (λ r → proj₁ r) INM) (pos 1 + negsuc 0) ≡ 0
      step1 =  (1+-1Is0 INM)
      step2 : transport (cong (λ r → proj₁ r) INM) (pos 1 + negsuc 0) ≡
                Add (transport (cong (λ r → proj₁ r) INM) (pos 1))
                (transport (cong (λ r → proj₁ r) INM) (negsuc 0))
      step2 = (ZNMagma+ INM (pos 1) (negsuc 0))
      step3 : Add (transport (cong (λ r → proj₁ r) INM) (pos 1))
                (transport (cong (λ r → proj₁ r) INM) (negsuc 0))
                ≡ 0
      step3 = sym step2  ∙ step1

transport-injectivity : {A B : Type}{x y : A}{z : B} → {A≡B : A ≡ B} → transport A≡B x ≡ z → transport A≡B y ≡ z → x ≡ y
transport-injectivity {A}{B}{x}{y}{z}{A≡B} tr1 tr2 = (sym (step2 x))  ∙ step1  ∙ (step2 y)
                           where
                             step1 : transport⁻ A≡B (transport A≡B x) ≡ transport⁻ A≡B (transport A≡B y)                           
                             step1 = cong (λ x' → transport⁻ A≡B  x') (tr1 ∙ (sym tr2))
                             step2 : ∀ u →  transport⁻ A≡B (transport A≡B u) ≡ u
                             step2 u = transport⁻Transport A≡B u


contrad : (INM : IntMagma ≡ NatMagma) → ⊥
contrad INM = posNotnegsuc 0 0 step2
           where
             step1 : pos 1 ≡ pos 0
             step1 = transport-injectivity {A = ℤ}{B = ℕ}{A≡B = cong fst INM} (1Is0 INM) (0Is0 INM)
             step2 : pos 0 ≡ negsuc 0
             step2 = cong predℤ step1
             
-- LEMMA PROVEN:
IntMagma≠NatMagma : (IntMagma* ≡ NatMagma*) → ⊥
IntMagma≠NatMagma ℤ*≡ℕ* = step0 ℤ*≡ℕ*
                where
                  step0 : IntMagma* ≡ NatMagma* → ⊥
                  step0 = contrad
                  

                 
 


