
{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}  --allowing k doesn't work with Cubical
{-# OPTIONS --no-main #-} 
{-# OPTIONS --cubical  #-}

module ClassicalLogicAFirstAttempt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Isomorphism 
open import Cubical.Data.Sum renaming (rec to recSum) -- annoying quirk, clashes with Empty.Base
open import Cubical.Data.Unit
open import Cubical.Data.Prod 

private 
  variable
    ℓ ℓ' ℓ'' : Level
private
  variable
      A B C : Type ℓ

----

--compPath...https://agda.readthedocs.io/en/latest/language/cubical.html (the old 'trans')
compPath : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)

compPath-ty : {ℓ : Level} {A B C : Type ℓ} → A ≡ B → B ≡ C → A ≡ C
compPath-ty {ℓ} {A} {B} {C} AB BC = compPath AB BC

------------------------------------------
--PRELIMINARIES
------------------------------------------

A→¬¬A :  {A : Type ℓ} → A → ¬ ¬ A
A→¬¬A {ℓ} {A} a na = na a

¬¬Unit→Unit : (nntt : ¬ ¬ Unit) → Unit
¬¬Unit→Unit nntt = tt

¬¬⊥→⊥ : ¬ ¬ ⊥ → ⊥
¬¬⊥→⊥ nn = nn (λ z → z)

⊥→¬¬⊥ : ⊥ → ¬ ¬ ⊥
⊥→¬¬⊥ n = λ z → z n

¬⊥ : ¬ ⊥
¬⊥ = λ z → z

⊥≡⊥ : ⊥ ≡ ⊥
⊥≡⊥ = refl

¬⊥≡¬⊥ : (¬ ⊥) ≡ (¬ ⊥)
¬⊥≡¬⊥ = refl

retract¬¬⊥→⊥-⊥→¬¬⊥ : retract {A = ¬ ¬ ⊥} {B = ⊥} ¬¬⊥→⊥ ⊥→¬¬⊥ 
retract¬¬⊥→⊥-⊥→¬¬⊥ a = rec (¬¬⊥→⊥ a)

¬¬⊥≡⊥ :  (¬ ¬ ⊥) ≡ ⊥
¬¬⊥≡⊥ = isoToPath (iso ¬¬⊥→⊥ ⊥→¬¬⊥ (λ ()) (retract¬¬⊥→⊥-⊥→¬¬⊥))

isProp⊤ : isProp Unit
isProp⊤ tt tt = refl

isProp¬A-hlp :  {A : Type ℓ} → (x : A) → (a b : ¬ A) → a x ≡ b x
isProp¬A-hlp {ℓ} {A} x a b = rec (a x) 

isProp¬A : {A : Type ℓ} → isProp (¬ A)
isProp¬A {ℓ} {A} x y = funExt λ z → isProp¬A-hlp z x y

isProp¬¬A : {A : Type ℓ} → isProp (¬ ¬ A)
isProp¬¬A = isProp¬A

isProp¬¬ : {A : Type ℓ} → isProp (¬ ¬ A)
isProp¬¬ = isProp¬A

isProp-Lift : {A : Type ℓ} → isProp A → isProp (Lift {ℓ} {(ℓ-suc ℓ)} A)
isProp-Lift {ℓ} {A} ispA (lift lower1) (lift lower2) = cong lift (ispA lower1 lower2)

isProp-subst  : {A : Type ℓ} → {B : Type ℓ} → isProp A → (A ≡ B) → isProp B
isProp-subst {ℓ} {A} {B} ispA AB = transport (cong (λ x → isProp x) AB) ispA

isProp-fun' : {A : Type ℓ} → {B : Type ℓ'} → isProp B → isProp (A → B)
isProp-fun' ispB f g = funExt (λ z → ispB (f z) (g z))

isProp-fun-dep : {A : Type ℓ} → {B : A → Type ℓ'} → ((x : A) → isProp (B x)) → isProp ((x : A) → (B x))
isProp-fun-dep ispBx p q  = funExt λ x → ispBx x (p x) (q x) 

isProp×'  : {ℓ  ℓ' : Level} -> {A : Type ℓ} → {B : Type ℓ'} → isProp A -> isProp B → isProp (A × B)
isProp×' {ℓ} {ℓ'} {A} {B} isPA isPB (x , y) (x1 , y1) i = (isPA x x1 i) , (isPB y y1 i)

--isProp⊥ : isProp ⊥
--isProp⊥ ()

isProp⊥→⊥ : isProp (¬ ⊥)
isProp⊥→⊥ x y = funExt (λ ())

isProp¬¬⊥ : isProp (¬ ¬ ⊥)
isProp¬¬⊥ x y = rec (¬¬⊥→⊥ x)

isProp¬¬A→¬¬B :  {A : Type ℓ} → {B : Type ℓ'} →  isProp ((¬ ¬ A) → (¬ ¬ B))
isProp¬¬A→¬¬B  {ℓ} {ℓ'} {A} {B} x y = funExt (λ z → isProp¬ ((x : B) → ⊥) (x z) (y z))

isPropA→¬B : {A : Type ℓ} → {B : Type ℓ'} →  isProp (A → (¬ B))
isPropA→¬B {ℓ} {ℓ'} {A} {B} x y = funExt (λ z → isProp¬ B (x z) (y z))

isPropA→¬¬B :  {A : Type ℓ} → {B : Type ℓ'} →  isProp (A → (¬ ¬ B))
isPropA→¬¬B  {ℓ} {ℓ'} {A} {B} x y = funExt (λ z → isProp¬ ((x : B) → ⊥) (x z) (y z))

isProp¬A→¬¬B :  {A : Type ℓ} → {B : Type ℓ'} →  isProp (A → (¬ ¬ B))
isProp¬A→¬¬B  {ℓ} {ℓ'} {A} {B} x y = funExt (λ z → isProp¬ ((x : B) → ⊥) (x z) (y z))

isProp¬A→¬B : {A : Type ℓ} → {B : Type ℓ'} →  isProp ((¬ A) → (¬ B))
isProp¬A→¬B {ℓ} {ℓ'} {A} {B} x y = funExt (λ z → isProp¬ B (x z) (y z))

isPropA→B : {A : Type ℓ} → {B : Type ℓ'} →  isProp B -> isProp (A -> B)
isPropA→B {ℓ} {ℓ'} {A} {B} ispB x1 y  = funExt (λ x → ispB (x1 x) (y x))

isPropA→A≡B→isPropB : {A B : Type ℓ} → isProp A → A ≡ B → isProp B
isPropA→A≡B→isPropB  {ℓ} {A} {B} ispA A≡B = transport (cong (λ x → isProp x) A≡B) ispA

isProp≡ : {A : Type ℓ} → (a b : A) → isProp A → isProp (a ≡ b)
isProp≡ a b h x y =  isProp→isSet h a b x y

Props≡' : {A B : Type ℓ} → isProp A → isProp B → (A → B) → (B → A) → (A ≡ B)
Props≡' {ℓ} {A} {B} ispA ispB ab ba = isoToPath (iso ab ba (λ b → ispB (ab (ba b)) b) (λ a → ispA (ba (ab a)) a)) 

isProps≡ : {A B : Type ℓ} → isProp A → isProp B → (isProp A) ≡ (isProp B)
isProps≡ {ℓ} {A} {B} ispA ispB = isoToPath (iso (λ _ → ispB) (λ _ → ispA) (λ x → isPropIsProp ispB x) (λ y → isPropIsProp ispA y))

isProp≡HLevel1 :  {A : Type ℓ} ->  (isProp A) ≡ (isOfHLevel 1 A)
isProp≡HLevel1 = refl

isProp⟷→isProp≡ : {A B : Type ℓ} → isProp A → isProp B → isProp (A ≡ B)
isProp⟷→isProp≡ {ℓ} {A} {B} ispA ispB  = transport (sym isProp≡HLevel1) isHLevel≡ 
                                          where
                                            isHLevel≡ :  isOfHLevel 1 (A ≡ B)
                                            isHLevel≡ = isOfHLevel≡ 1 ispA ispB
                                                           
Unit≡¬¬Unit : Unit ≡ (¬ ¬ Unit)
Unit≡¬¬Unit = isoToPath (iso (λ _ z → z tt) (λ _ → tt) (isProp¬A (λ z → z tt)) λ x → refl)

⊥≡¬Unit :  ⊥ ≡ (¬ Unit)
⊥≡¬Unit = isoToPath (iso (λ z _ → z) (λ z → z tt) (λ x → refl) (λ ()))

A≡B→¬A≡¬B : {A B : Type ℓ} → (A ≡ B) → (¬ A) ≡ (¬ B)  
A≡B→¬A≡¬B A≡B = cong ¬_ A≡B

A≡B→¬¬A≡¬¬B : {A B : Type ℓ} → (A ≡ B) → (¬ ¬ A) ≡ (¬ ¬ B)  
A≡B→¬¬A≡¬¬B A≡B = A≡B→¬A≡¬B (A≡B→¬A≡¬B A≡B)

¬⊥≡¬¬Unit : (¬ ⊥) ≡ (¬ ¬ Unit)
¬⊥≡¬¬Unit = A≡B→¬A≡¬B ⊥≡¬Unit

¬⊥≡Unit : (¬ ⊥) ≡ Unit
¬⊥≡Unit = ¬⊥≡¬¬Unit ∙ (sym Unit≡¬¬Unit)

A→Unit : A → (A → Unit)
A→Unit a = λ _ → tt

¬A≡A→⊥ : {A : Type ℓ} → (Unit ≡ ⊥) → ⊥
¬A≡A→⊥ aa = transport aa tt

A→B≡A→C :  {A : Type ℓ} → {B C : Type ℓ'} → (B ≡ C) → (A → B) ≡ (A → C)
A→B≡A→C {A = A} {C = C}  bc = cong (λ a → (x : A) → a) bc
 
-- The following function was thanks to Agda Zulip 
A≡B×C≡D→A×C≡B×D : {A B : Type ℓ} → {C D : Type ℓ'} → ((A ≡ B) × (C ≡ D)) → ((A × C) ≡ (B × D)) 
A≡B×C≡D→A×C≡B×D  {ℓ}{ℓ'}{A}{B}{C}{D} (A≡B , C≡D) i = ((A≡B i) × (C≡D i))

A≡BInA×C :  {A B : Type ℓ} → {C D : Type ℓ'} → (A ≡ B) → (C ≡ D) → (A × C) ≡ (B × D)
A≡BInA×C {ℓ}{ℓ'}{A}{B}{C}{D} ab cd = congP (λ i -> λ x → ab i × x) cd

A≡BInA⊎C :  {A B : Type ℓ} → {C D : Type ℓ'} → (A ≡ B) → (C ≡ D) → (A ⊎ C) ≡ (B ⊎ D)
A≡BInA⊎C {ℓ}{ℓ'}{A}{B}{C}{D} ab cd = congP (λ i -> λ x → ab i ⊎ x) cd

A≡BInA→C :  {A B : Type ℓ} → {C D : Type ℓ'} → (A ≡ B) → (C ≡ D) → (A → C) ≡ (B → D)
A≡BInA→C  {ℓ}{ℓ'}{A}{B}{C}{D} A≡B C≡D  = congP (λ i → λ x → (A≡B i) → x) C≡D

AA'BB'≡ABA'B' : {A A' : Type ℓ} → {B B' : Type ℓ'} → (AA' : A ≡ A') → (BB' : B ≡ B') → (A × B) ≡ (A' × B')
AA'BB'≡ABA'B' {ℓ} {ℓ'} {A} {B} AA' BB' = λ i → AA' i × BB' i

AA'BB'≡AB⊎A'B' : {A A' : Type ℓ} → {B B' : Type ℓ'} → (AA' : A ≡ A') → (BB' : B ≡ B') → (A ⊎ B) ≡ (A' ⊎ B')
AA'BB'≡AB⊎A'B' {ℓ} {ℓ'} {A} {B} AA' BB' = λ i → AA' i ⊎ BB' i

¬¬implication : {A : Type ℓ}  → {B : Type ℓ'} →  ¬ ¬ ((¬ ¬ A) -> (¬ ¬ B)) -> ((¬ ¬ A) -> (¬ ¬ B))
¬¬implication x = λ z z₁ → z (λ z₂ → x (λ z₃ → z₃ (λ z₄ → z₄ z₂) z₁))

A¬¬A :  {A : Type ℓ} → (A → ¬ ¬ A)
A¬¬A {ℓ} {A} a na = na a

¬¬¬A¬A : {A : Type ℓ} → (¬ ¬ ¬ A → ¬ A)
¬¬¬A¬A nnna a = nnna (A¬¬A a)

¬A¬¬¬A :  {A : Type ℓ} → (¬ A → ¬ ¬ ¬ A)
¬A¬¬¬A  {ℓ} {A} na nna = nna na

¬¬¬A≡¬A :  {A : Type ℓ} → (¬ ¬ ¬ A) ≡ (¬ A)
¬¬¬A≡¬A  {ℓ} {A} = isoToPath (iso ¬¬¬A¬A ¬A¬¬¬A (λ b → isProp¬ A (¬¬¬A¬A (¬A¬¬¬A b)) b) (λ a → isProp¬ ((x : (x₁ : A) → ⊥) → ⊥) (¬A¬¬¬A (¬¬¬A¬A a)) a))

nnAnB→nab : {A B : Type ℓ} → ¬ ((¬ A) ≡ (¬ B)) → ¬ ( A ≡ B )
nnAnB→nab ab x = ab (A≡B→¬A≡¬B x)

nnAnB→nab4 : {A B : Type ℓ} → ¬ ((¬ ¬ A) ≡ (¬ ¬ B)) → ¬ (A ≡ B)
nnAnB→nab4 nnnn = nnAnB→nab (nnAnB→nab nnnn)

nnAnB→nab2 : {A B : Type ℓ} → ¬ ((¬ ¬ ¬ A) ≡ (¬ ¬ ¬ B)) → ¬ ((¬ A) ≡ (¬ B) )
nnAnB→nab2 = λ x → nnAnB→nab ((nnAnB→nab x)) 

nnAnB→nab3 : {A B : Type ℓ} → ¬ ((¬ ¬ ¬ A) ≡ (¬ ¬ ¬ B)) → ¬ ( A ≡ B )
nnAnB→nab3 = λ x → nnAnB→nab (nnAnB→nab (nnAnB→nab x)) 

nnABnnnAnB : {A B : Type ℓ} → ¬ ¬ (A ≡ B) → ¬ ¬ ((¬ A) ≡ (¬ B))
nnABnnnAnB nnnnab x =  nnnnab something where something = nnAnB→nab x

nnABnnnnAnnB : {A B : Type ℓ} → ¬ ¬ (A ≡ B) → ¬ ¬ ((¬ ¬ A) ≡ (¬ ¬ B))
nnABnnnnAnnB nnnnab x =  nnABnnnAnB (nnABnnnAnB nnnnab) (λ x₁ → x x₁)

sym¬ :  {A : Type ℓ} → {a b :  A} → ¬ (a ≡ b) → ¬ (b ≡ a)
sym¬ nab = λ x → nab (sym x)

subst≡-in¬  : {A : Type ℓ} → {a b c :  A} → ¬ (a ≡ b) → (b ≡ c) -> ¬ (a ≡ c) 
subst≡-in¬ nab bc x = nab (compPath x (sym bc))

¬¬A¬¬A→B : ¬ ¬ A → ¬ ¬ (A → B) → ¬ ¬ B
¬¬A¬¬A→B nna nnAB x = nnAB (λ z → nna (λ z₁ → x (z z₁)))

A→B→¬B→¬A : {A : Type ℓ} → {B : Type ℓ'} → (A → B) → (¬ B) → (¬ A)
A→B→¬B→¬A = λ z z₁ z₂ → z₁ (z z₂)

¬¬A→B→¬¬B→C→¬¬A→C : ¬ ¬ (A → B) → ¬ ¬ (B → C) → ¬ ¬ (A → C)
¬¬A→B→¬¬B→C→¬¬A→C nnAB nnBC x = nnAB (λ z → nnBC (λ z₁ → x (λ z₂ → z₁ (z z₂))))

¬¬A¬¬B→¬¬AB : {A : Type ℓ} → {B : Type ℓ'} → ¬ ¬ A → ¬ ¬ B → ¬ ¬ ((¬ ¬ A) × (¬ ¬ B))
¬¬A¬¬B→¬¬AB nnA nnB = λ x → x ((λ x → nnB (λ _ → nnA x)) , nnB)

¬¬A¬¬B→¬¬AB2 : {A : Type ℓ} → {B : Type ℓ'} → ¬ ¬ A → ¬ ¬ B → ¬ ¬ (A × B)
¬¬A¬¬B→¬¬AB2 nnA nnB = λ z → nnB (λ z₁ → nnA (λ z₂ → z (z₂ , z₁)))

¬A→¬A×B : ¬ A → ¬ (A × B)
¬A→¬A×B nA (x , x₁) = nA x

¬B→¬A×B : ¬ B → ¬ (A × B)
¬B→¬A×B nB (x , x₁) = nB x₁

¬¬AB→nnA :  {A : Type ℓ} → {B : Type ℓ'} →  ¬ ¬ (A × B) → ¬ ¬ A 
¬¬AB→nnA {ℓ} {ℓ'} {A} {B} nnAB nAB = nnAB (¬A→¬A×B nAB)

¬¬AB→nnB : {A : Type ℓ} → {B : Type ℓ'} →  ¬ ¬ (A × B) → ¬ ¬ B
¬¬AB→nnB  {ℓ} {ℓ'} {A} {B} nnAB nAB = nnAB (¬B→¬A×B nAB)

nAnB→nAorB : {A : Type ℓ} → {B : Type ℓ'} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
nAnB→nAorB (x₁ , x₂) (inl x) = x₁ x
nAnB→nAorB (x , x₁) (inr y) = x₁ y

nAorB→nAnB : {A : Type ℓ} → {B : Type ℓ'} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
nAorB→nAnB nAorB = (λ z → nAorB (inl z)) , λ z → nAorB (inr z)

isPropnor : {A : Type  ℓ} -> {B : Type  ℓ'} ->  (a b : (¬ A) × (¬ B)) -> (a ≡ b)
isPropnor  {ℓ}{ℓ'} {A} {B} (x , y) (x1 , y1) = isProp×' (isProp¬ A) (isProp¬ B) (x , y) (x1 , y1) 

nAnB≡nAorB : {A : Type ℓ} → {B : Type ℓ'} → ((¬ A) × (¬ B)) ≡ (¬ (A ⊎ B))
nAnB≡nAorB {ℓ} {ℓ'} {A} {B}  = isoToPath (iso nAnB→nAorB nAorB→nAnB (λ b → isProp¬ (A ⊎ B) (nAnB→nAorB ((λ x → b (inl x)) , (λ x → b (inr x)))) b) λ a → isPropnor ((λ x → nAnB→nAorB a (inl x)) , (λ x → nAnB→nAorB a (inr x))) a)

¬¬AorB→NnAandnB : {A : Type ℓ} → {B : Type ℓ'} → ¬ ¬ (A ⊎ B) → ¬ ((¬ A) × (¬ B))
¬¬AorB→NnAandnB {ℓ} {ℓ'} {A} {B} nnAB nAnB = nnAB (nAnB→nAorB nAnB)
 
NnnnAandnnnB→NnAandnB : {A : Type ℓ} → {B : Type ℓ'} → ¬ ((¬ ¬ ¬ A) × (¬ ¬ ¬ B)) → ¬ ((¬ A) × (¬ B))
NnnnAandnnnB→NnAandnB  {ℓ} {ℓ'} {A} {B} nnn = transport (A≡B→¬A≡¬B (AA'BB'≡ABA'B'  ¬¬¬A≡¬A  ¬¬¬A≡¬A)) nnn 

NAandnnnB≡NnAandnB : {A : Type ℓ} → {B : Type ℓ'} → (¬ ((A) × (¬ ¬ ¬ B))) ≡ (¬ ((A) × (¬ B)))
NAandnnnB≡NnAandnB {ℓ} {ℓ'} {A} {B} = A≡B→¬A≡¬B (AA'BB'≡ABA'B' refl ¬¬¬A≡¬A )                  

NnAandnB→¬¬AorB : {A : Type ℓ} → {B : Type ℓ'} → ¬ ((¬ A) × (¬ B)) → ¬ ¬ (A ⊎ B) 
NnAandnB→¬¬AorB nnAorB v =  nnAorB ((λ x → v (inl x)) , (λ x → v (inr x)))

NnAandnB≡¬¬AorB : {A : Type ℓ} → {B : Type ℓ'} → (¬ ((¬ A) × (¬ B))) ≡ (¬ ¬ (A ⊎ B))
NnAandnB≡¬¬AorB {ℓ} {ℓ'} {A} {B} = isoToPath (iso NnAandnB→¬¬AorB ¬¬AorB→NnAandnB (λ b → isProp¬ ((x : A ⊎ B) → ⊥) (NnAandnB→¬¬AorB (¬¬AorB→NnAandnB b)) b) λ a → isProp¬ (((x : A) → ⊥) × ((x : B) → ⊥)) (¬¬AorB→NnAandnB (NnAandnB→¬¬AorB a)) a)

NnAandnB≡¬¬AorB2 : {A : Type ℓ} → {B : Type ℓ'} → (¬ ¬ ((¬ A) × (¬ B))) ≡ (¬ (A ⊎ B))
NnAandnB≡¬¬AorB2 = compPath (cong (λ x → ¬ x) NnAandnB≡¬¬AorB) ¬¬¬A≡¬A

¬¬AorB2→NnAandnB  : {A : Type ℓ} → {B : Type ℓ'} → (¬ (A ⊎ B)) → (¬ ¬ ((¬ A) × (¬ B)))
¬¬AorB2→NnAandnB {ℓ} {ℓ'} {A} {B} x = transport (sym NnAandnB≡¬¬AorB2)  x 

¬¬¬¬A⊎¬¬B→¬¬A⊎B :  {A : Type ℓ} → {B : Type ℓ'} → (¬ ¬ ((¬ ¬ A) ⊎ (¬ ¬ B))) -> (¬ ¬ (A ⊎ B))
¬¬¬¬A⊎¬¬B→¬¬A⊎B {ℓ}{ℓ'} {A} {B} x = NnAandnB→¬¬AorB (NnnnAandnnnB→NnAandnB (¬¬AorB→NnAandnB x))

A→B→¬¬A→¬¬B :  {A : Type ℓ} → {B : Type ℓ'} → (prf : A → B) → ((¬ ¬ A) → (¬ ¬ B))
A→B→¬¬A→¬¬B  {ℓ}{ℓ'} {A} {B} x  = λ z z₁ → z (λ z₂ → z₁ (x z₂))

A⊎B→¬¬A⊎¬¬B : {A : Type ℓ} → {B : Type ℓ'} → (prf : A ⊎ B) → ((¬ ¬ A) ⊎ (¬ ¬ B))
A⊎B→¬¬A⊎¬¬B (inl x) = inl (λ y → y x)
A⊎B→¬¬A⊎¬¬B (inr x) = inr (λ y → y x)

¬¬A⊎B→¬¬¬¬A⊎¬¬B :  {A : Type ℓ} → {B : Type ℓ'} →  (¬ ¬ (A ⊎ B)) → (¬ ¬ ((¬ ¬ A) ⊎ (¬ ¬ B)))
¬¬A⊎B→¬¬¬¬A⊎¬¬B  {ℓ}{ℓ'} {A} {B} x  = A→B→¬¬A→¬¬B A⊎B→¬¬A⊎¬¬B x               

NnnAandnB→¬¬nnAornB : {A : Type ℓ} → {B : Type ℓ'} → ¬ ¬ ((¬ A) × (¬ B)) → ((¬ A) × (¬ B))
NnnAandnB→¬¬nnAornB nnnAnB = (¬¬¬A¬A (¬¬AB→nnA nnnAnB)) , ((¬¬¬A¬A (¬¬AB→nnB nnnAnB)))

NnnnAandnnB→¬¬nnnAornnB : {A : Type ℓ} → {B : Type ℓ'} → ¬ ¬ ((¬ ¬ A) × (¬ ¬ B)) → ((¬ ¬ A) × (¬ ¬ B))
NnnnAandnnB→¬¬nnnAornnB = NnnAandnB→¬¬nnAornB 

NnnAandnB≡¬¬nnAornB : {A : Type ℓ} → {B : Type ℓ'} → (¬ ¬ ((¬ A) × (¬ B))) ≡ ((¬ A) × (¬ B))
NnnAandnB≡¬¬nnAornB {ℓ}{ℓ'}{A}{B} = compPath NnnAandnB≡¬¬nnAornB-hlp  (compPath ¬¬¬A≡¬A (sym (nAnB≡nAorB {ℓ}{ℓ'}{A}{B}))) 
                                        where
                                           NnnAandnB≡¬¬nnAornB-hlp : (¬ ¬ ((¬ A) × (¬ B))) ≡ (¬ ¬ (¬ (A ⊎ B)))
                                           NnnAandnB≡¬¬nnAornB-hlp = cong (λ x → ¬ ¬ x ) nAnB≡nAorB

Nand→nAndnn  : {A : Type ℓ} → {B : Type ℓ'} →  (¬ ((¬ ¬ A) × (¬ ¬ B))) → (¬ (A × B)) 
Nand→nAndnn nnn (x , y) = nnn ((λ z → z x) , (λ z → z y))

NAnd→nn  : {A : Type ℓ} → {B : Type ℓ'} → (¬ (A × B)) → (¬ ((¬ ¬ A) × (¬ ¬ B))) 
NAnd→nn x (y , z) = z (λ z → y (λ z₁ → x (z₁ , z)))

-- a bit ugly due to use of automatic proof
Nandnn≡n×  : {A : Type ℓ} → {B : Type ℓ'} →  (¬ ((¬ ¬ A) × (¬ ¬ B))) ≡ (¬ (A × B)) 
Nandnn≡n× {ℓ}{ℓ'}{A}{B} = isoToPath (iso Nand→nAndnn NAnd→nn (λ b → isProp¬ (A × B) (Nand→nAndnn (NAnd→nn b)) b)
                                    (λ a → isProp¬ (((x : (x₁ : A) → ⊥) → ⊥) × ((x : (x₁ : B) → ⊥) → ⊥)) (NAnd→nn (Nand→nAndnn a)) a))

Nnandnn≡n×  : {A : Type ℓ} → {B : Type ℓ'} →  (¬ ¬ ((¬ ¬ A) × (¬ ¬ B))) ≡ (¬ ¬ (A × B)) 
Nnandnn≡n× {ℓ}{ℓ'}{A}{B} = cong (λ x -> ¬ x) Nandnn≡n×

¬¬AorA→¬¬A : {A : Type ℓ} → ¬ ¬ (A ⊎ A) → ¬ ¬ A
¬¬AorA→¬¬A nnAorA x = rec (nnAorA (nAnB→nAorB (x , x)))

¬A→¬AorA  : {A : Type ℓ} → ¬ A → ¬ (A ⊎ A)
¬A→¬AorA {ℓ} {A} na (inl x) = na x
¬A→¬AorA {ℓ} {A} na (inr x) = na x

¬A×¬A≡A : {A : Type ℓ} → ((¬ A) × (¬ A)) ≡ (¬ A)
¬A×¬A≡A {ℓ}{A} = isoToPath (iso (λ x → proj₁ x) (λ y → y , y) (λ a → refl) (λ b → isProp×' (λ u → isProp¬ A u) (isProp¬ A) (proj₁ b , proj₁ b) b))

A→B→B→C→A→C1 : {A : Type ℓ} → {B : A -> Type  ℓ'}  → {C : (A -> Type  ℓ') -> Type  ℓ''} → ((a : A) → (B a)) → ((b : (A -> Type ℓ')) → (C b)) → ((a : A) → (C B))
A→B→B→C→A→C1  {ℓ} {ℓ'} {ℓ''} {A} {B} {C} = λ _ z a → z B

----

-- a constructive double implication
record _⟷_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    AtoB : A → B
    BtoA : B → A 

mkA⟷B :  {A : Type ℓ} → {B : Type ℓ'} → (A → B) → (B → A) → A ⟷ B
mkA⟷B AB BA = record { AtoB = AB ; BtoA = BA }

Props≡ :  {A B : Type ℓ} → isProp A → isProp B → (A ⟷ B) → (A ≡ B)
Props≡ {ℓ} {A} {B} ispA ispB ab = Props≡' ispA ispB (_⟷_.AtoB ab) (_⟷_.BtoA ab)

¬isProp→ : {A : Type ℓ} → (a b : A) → ¬ (isProp (a ≡ b)) → ¬ (isProp A)
¬isProp→ a b = A→B→¬B→¬A (isProp≡ a b) 

----
--Decidability

--data Dec (P : Type ℓ) : Type ℓ where
--  yes : ( p :   P) → Dec P
--  no  : (¬p : ¬ P) → Dec P

data DecEq (P : Type ℓ) : Type ℓ where
  decEq : (∀ {p q : P} → Dec (p ≡ q)) → DecEq P

decP : {P : Type ℓ} → Dec P → ¬ ¬ P → P
decP (yes p) nnp = p
decP (no ¬p) nnp = rec (nnp ¬p)

decEqIsProp≡ : {P : Type ℓ} → Dec P → isProp P → (¬ ¬ P) ≡ P      
decEqIsProp≡  dp isp = isoToPath (iso (decP dp) A¬¬A (λ b → isp (decP dp (λ z → z b)) b) (λ y -> isProp¬ _ (A¬¬A (decP dp y)) y ))

decEq→≡ : {P : Type ℓ} → {p q : P} → DecEq P → Dec (p ≡ q)
decEq→≡ (decEq x) = x

squashDec : {P : Type ℓ}{x x' : P} → DecEq P → ¬ ¬ (x ≡ x') → x ≡ x'
squashDec {ℓ} {P} {x} {x'} (decEq y) nnxx = decP y nnxx

decApply :  ∀ {ℓ} {ℓ'} {A : Set ℓ} {C : Set ℓ'} {x x' : A} → (decC : DecEq C) → (f g : A → C) → Dec (f x ≡ g x')
decApply {ℓ} {ℓ'} {A} {C} {x} {x'} (decEq z) f g = z

dec→ : {A : Type  ℓ} -> {B : Type  ℓ'} → Dec A → Dec B → Dec (A → B)
dec→ {ℓ} {ℓ'} {A} {B} (yes p) (yes p₁) = yes (λ x → p₁)
dec→ {ℓ} {ℓ'} {A} {B} (yes p) (no ¬p) = no (λ z → ¬p (z p))
dec→ {ℓ} {ℓ'} {A} {B} (no ¬p) (yes p) = yes (λ x → p)
dec→ {ℓ} {ℓ'} {A} {B} (no ¬p) (no ¬p₁) = yes (λ a → rec (¬p a))

isPropDec' : {A : Type ℓ} → (isProp A) → isProp (Dec A)
isPropDec' {ℓ} {A} = isPropDec

¬¬dec : {A : Type ℓ} →  ¬ ¬ (Dec A)
¬¬dec = λ z → z (no (λ z₁ → z (yes z₁)))

isPropLiftDecA : {A : Type ℓ} → (isProp A) → isProp (Lift {ℓ}{ℓ-suc ℓ} (Dec A))
isPropLiftDecA {ℓ} {A} Aprop (lift (a)) (lift (b)) = cong lift (isPropDec Aprop a b)

-----------------------------------------
-----------------------------------------
-- BASIC CONSTRUCTS FOR CLASSICAL LOGIC   *****
-----------------------------------------
-- A Goedel fragment in Cubical Agda
-- Defining a classical 'true' as isTrue
-----------------------------------------

infixr 20 _⇒_

-- IsTrue (defines classical 'truth')
IsTrue : Type ℓ → Type ℓ
IsTrue A = ¬ ¬ A

-- Nor 
Nor : (A : Type  ℓ) -> (B : Type  ℓ') -> Type (ℓ-max ℓ ℓ') 
Nor A B = (¬ A) × (¬ B)

-- And predicate calculus...
-- Notice that the syntax is not the usual mathematical
-- syntax in that B is a lambda abstraction rather than
-- an expression containing a previously introduced
-- variable. There are ways to make it appear more
-- familiar, but full generality is perhaps simpler by
-- using the notation natural to the Type Theory, rather
-- than imposing standard mathematical practice on the
-- type theory. It requires getting used to though.

Forall : (A : Type ℓ) -> (B : A → Type ℓ') -> Type (ℓ-max (ℓ) (ℓ')) 
Forall A B = (x : A) → IsTrue (B x)

-----------------------------------------

IsTrue⊥ : IsTrue ⊥ → ⊥
IsTrue⊥ = λ z → z (λ z₁ → z₁)

isTrue⊤ : Unit → IsTrue Unit
isTrue⊤ tt = λ z → z tt

isPropIsTrue : {A : Type  ℓ} -> isProp (IsTrue A)   -- a useful feature of classical logic 
isPropIsTrue = isProp¬¬  

isPropNor : {A : Type  ℓ} -> {B : Type  ℓ'} → isProp (Nor A B)
isPropNor {ℓ} {ℓ'} {A} {B} = isPropnor  

isPropForall-hlp : {A : Type ℓ} → {B : A → Type ℓ'} → isProp (∀ x → IsTrue (B x))   
isPropForall-hlp {ℓ} {ℓ'} {A} {B} = isProp-fun-dep (λ x → isPropIsTrue) 

isPropForall : {A : Type ℓ} → {B : A → Type ℓ'} → isProp (Forall A B)
isPropForall {ℓ} {ℓ'} {A} {B} = isPropForall-hlp

-----------------------------------------
-- What it means for this 'Goedel fragment' to be 'classical'
-----------------------------------------
-- An expression is invariant when IsTrue is
-- applied to a definition and/or any number of its
-- arguments that cannot be inferred. Or it
-- is equivalent to another classical definition via ≡. 

pure : {A : Type ℓ} -> (x : A) -> IsTrue A
pure x = λ z → z x

NonFalsifiable : Type ℓ → Type ℓ
NonFalsifiable = IsTrue

NonFalsifiable≡IsTrue : {A : Type  ℓ} -> NonFalsifiable A ≡ IsTrue A
NonFalsifiable≡IsTrue = refl

IsFalse : (A : Type ℓ) → Type ℓ  
IsFalse A = Nor A A

IsTrueClassical : {A : Type ℓ} -> IsTrue A ≡ (IsTrue (IsTrue A))
IsTrueClassical {ℓ} {A} =  sym ¬¬¬A≡¬A

¬Classical1 : {A : Type ℓ} -> (¬ A) ≡ IsTrue (¬ A)
¬Classical1 {ℓ} {A} =  sym ¬¬¬A≡¬A

¬Classical2 : {A : Type ℓ} -> (¬ A) ≡ (¬ (IsTrue A))
¬Classical2 {ℓ} {A} =  sym ¬¬¬A≡¬A

----
-- that IsFalse is equivalent to ¬ 
IsFalse→¬ : {A : Type  ℓ} -> IsFalse A → ¬ A
IsFalse→¬ {ℓ} {A} (x , y) = y

¬→IsFalse  : {A : Type  ℓ} -> ¬ A → IsFalse A
¬→IsFalse {ℓ} {A} = λ z → z , z

IsFalse≡¬-retract : {A : Type  ℓ} -> (y : IsFalse A) →  ¬→IsFalse (IsFalse→¬ y) ≡ y
IsFalse≡¬-retract {ℓ} {A} (a , b) =  isProp×' (isProp¬ A) (isProp¬ A) (b , b) (a , b)
                                                                      
IsFalse≡¬ : {A : Type  ℓ} -> (IsFalse A) ≡ (¬ A)
IsFalse≡¬ {ℓ} {A} = isoToPath (iso IsFalse→¬ ¬→IsFalse (λ x → refl) λ y → IsFalse≡¬-retract y ) 

--applying this to get an isProp theorem for IsFalse 
isPropIsFalse  : {A : Type  ℓ} -> isProp (IsFalse A)
isPropIsFalse {ℓ} {A} =  transport (cong (λ x → isProp x) (sym IsFalse≡¬)) (isProp¬ A)

-- and to prove Classicality:
IsFalseClassical1 : {A : Type ℓ} -> IsFalse A ≡ (IsTrue (IsFalse A))
IsFalseClassical1  {ℓ} {A} = compPath IsFalse≡¬ (compPath ¬Classical1 (cong IsTrue (sym IsFalse≡¬)))

IsFalseClassical2 : {A : Type ℓ} -> IsFalse A ≡ (IsFalse (IsTrue A))
IsFalseClassical2  {ℓ} {A} = compPath IsFalse≡¬ (compPath ¬Classical2 (sym IsFalse≡¬))

-- and we can get 'isPropIsFalse' another way (ie not using isPropIsFalse):
isPropIsFalse'  : {A : Type  ℓ} -> isProp (IsFalse A)
isPropIsFalse' {ℓ} {A} = isPropA→A≡B→isPropB isPropIsTrue (sym IsFalseClassical1)

----
-- Nor
Nor≡ : {A : Type  ℓ} -> {B : Type  ℓ'} → Nor A B ≡ (¬ A) × (¬ B) 
Nor≡ {ℓ}{ℓ'} {A} {B} = refl 

NorClassical1 : {A : Type  ℓ} -> {B : Type  ℓ'} -> Nor A B ≡ (IsTrue (Nor A B))
NorClassical1 {ℓ}{ℓ'} {A} {B} = sym NnnAandnB≡¬¬nnAornB    

NorClassical2 : {A : Type  ℓ} -> {B : Type  ℓ'} -> Nor A B ≡ (Nor (IsTrue A) B)
NorClassical2  {ℓ}{ℓ'} {A} {B} = compPath Nor≡ (compPath (A≡BInA×C (sym ¬¬¬A≡¬A) refl) refl)

NorClassical3 : {A : Type  ℓ} -> {B : Type  ℓ'} -> Nor A B ≡ (Nor A (IsTrue B))
NorClassical3  {ℓ}{ℓ'} {A} {B} = compPath Nor≡ (compPath (A≡BInA×C refl (sym  ¬¬¬A≡¬A)) refl)

 -- the usual idea of 'nor' constructively and classically as "not (or A B)" 
Nor≡nor : {A : Type  ℓ} -> {B : Type  ℓ'} → Nor A B ≡ (¬ (A ⊎ B)) 
Nor≡nor = nAnB≡nAorB

Nor¬A¬B≡¬¬A×¬¬A : {A : Type  ℓ} -> {B : Type  ℓ'} → Nor (¬ A) (¬ B) ≡ (¬ ¬ A) × (¬ ¬ B) 
Nor¬A¬B≡¬¬A×¬¬A  {ℓ}{ℓ'} {A} {B} = compPath Nor≡nor (sym nAnB≡nAorB)

----
-- A classical Or   -- notice that this is  (¬ ¬ (A ⊎ B)) and is not constructive (A ⊎ B)
-- That this is 'classical' follows by structural induction, and need not be included here. 

Or : (A : Type  ℓ) -> (B : Type  ℓ') -> Type (ℓ-max ℓ ℓ') 
Or A B = ¬ (Nor A B)

Or≡¬Nor :  {A : Type  ℓ} -> {B : Type  ℓ'} -> (Or A B) ≡ (¬ (Nor A B))
Or≡¬Nor = refl

Or-absurd : {A : Type  ℓ} -> {B : Type  ℓ'} -> ¬ A → ¬ B → Or A B → ⊥
Or-absurd  {ℓ}{ℓ'} {A} {B} = λ z z₁ z₂ → z₂ (z , z₁)

Or≡¬¬⊎ : {A : Type  ℓ} -> {B : Type  ℓ'} -> (Or A B) ≡ (¬ ¬ (A ⊎ B)) 
Or≡¬¬⊎ = compPath Or≡¬Nor (A≡B→¬A≡¬B Nor≡nor) 

EM' : (A : Type ℓ) → IsTrue (A ⊎ (¬ A))
EM' = λ A z → z (inr (λ x → z (inl x)))

EM :  {A : Type ℓ} → (Or A (¬ A))
EM {A = A} = transport (sym Or≡¬¬⊎) (λ z → z (inr (λ x → z (inl x))))

mkOr1 : {A : Type  ℓ} -> {B : Type  ℓ'} → IsTrue A → (Or A B)
mkOr1 {A = A} {B = B} a = transport (sym Or≡¬¬⊎) lemma
                          where
                            lemma : (¬ ¬ (A ⊎ B))
                            lemma = λ z → a (λ z₁ → z (inl z₁))

mkOr2 : {A : Type  ℓ} -> {B : Type  ℓ'} → IsTrue B → (Or A B)
mkOr2 {A = A} {B = B} a = transport (sym Or≡¬¬⊎) lemma
                          where
                            lemma : (¬ ¬ (A ⊎ B))
                            lemma = λ z → a (λ z₁ → z (inr z₁))

-- We have:
isPropOr : {A : Type  ℓ} -> {B : Type  ℓ'} -> isProp (Or A B)
isPropOr  {ℓ}{ℓ'} {A} {B} = isProp¬ (((x : A) → ⊥) × ((x : B) → ⊥))   

----
-- A classical 'Nand' likewise:

Nand : (A : Type  ℓ) -> (B : Type  ℓ') -> Type (ℓ-max ℓ ℓ') 
Nand A B = ¬ (Nor (¬ A) (¬ B))

Nand≡ : {A : Type  ℓ} -> {B : Type  ℓ'} -> Nand A B ≡ (¬ (Nor (¬ A) (¬ B))) -- doubles as 'classicality' condition
Nand≡ = refl

Nand≡not¬¬A×¬¬B : {A : Type  ℓ} -> {B : Type  ℓ'} -> Nand A B ≡ (¬ ((¬ ¬ A) × (¬ ¬ B)))
Nand≡not¬¬A×¬¬B {ℓ}{ℓ'}{A}{B} = compPath Nand≡ (cong (λ x -> ¬ x) Nor¬A¬B≡¬¬A×¬¬A)

Nand≡nand : {A : Type  ℓ} -> {B : Type  ℓ'} -> (Nand A B) ≡ (¬ (A × B))
Nand≡nand  {ℓ}{ℓ'} {A} {B} = compPath Nand≡not¬¬A×¬¬B Nandnn≡n×

----
-- This leads to a classical And. As with Or it is not the constructive (A × B)

And : (A : Type  ℓ) -> (B : Type  ℓ') -> Type (ℓ-max ℓ ℓ') 
And A B = ¬ (Nand A B)

And≡¬¬A×¬¬B : {A : Type ℓ} → {B : Type ℓ'} → And A B ≡ (¬ ¬ A) × (¬ ¬ B)
And≡¬¬A×¬¬B  {ℓ}{ℓ'} {A} {B} = NnnAandnB≡¬¬nnAornB 

And≠¬A⊎¬B : {A : Type ℓ} → {B : Type ℓ'} → And A B ≡ (¬ ((¬ A) ⊎ (¬ B)))
And≠¬A⊎¬B = compPath refl NnAandnB≡¬¬AorB2

And≡Nor¬A¬B : {A : Type ℓ} → {B : Type ℓ'} → And A B ≡ Nor (¬ A) (¬ B)
And≡Nor¬A¬B {ℓ}{ℓ'} {A} {B} = compPath And≠¬A⊎¬B (sym Nor≡nor)

----
-- We need a classical implication:
_⇒_ :  (A : Type  ℓ) -> (B : Type  ℓ') -> Type (ℓ-max ℓ ℓ')
A ⇒ B = IsTrue A → IsTrue B

⇒≡ : {A : Type  ℓ} -> {B : Type  ℓ'} -> A ⇒ B ≡ (IsTrue A → IsTrue B)
⇒≡ = refl

isProp⇒ :  {A : Type ℓ} → {B : Type ℓ'} →  isProp (IsTrue A → IsTrue B)
isProp⇒ {ℓ} {ℓ'} {A} {B} x y = funExt λ z → isProp¬¬ (x z) (y z)

⇒Classical-hlp : {A : Type  ℓ} -> {B : Type  ℓ'} -> IsTrue (A ⇒ B) → (A ⇒ B)
⇒Classical-hlp  {ℓ}{ℓ'} {A} {B} ist x y = x (λ z → ist (λ z₁ → z₁ (λ z₂ → z₂ z) y))

⇒Classical1 : {A : Type  ℓ} -> {B : Type  ℓ'} -> A ⇒ B ≡ IsTrue (A ⇒ B) 
⇒Classical1 {ℓ}{ℓ'} {A} {B} = isoToPath (iso A¬¬A ⇒Classical-hlp (λ x → isProp¬¬ (A¬¬A (⇒Classical-hlp x)) x) (λ y → isProp⇒ (⇒Classical-hlp (A¬¬A y)) y))

⇒Classical2 : {A : Type  ℓ} -> {B : Type  ℓ'} -> A ⇒ B ≡ ((IsTrue A) ⇒ B) 
⇒Classical2 {ℓ}{ℓ'} {A} {B} = compPath ⇒≡ (compPath (A≡BInA→C IsTrueClassical refl) (sym ⇒≡)) 

⇒Classical3 : {A : Type  ℓ} -> {B : Type  ℓ'} -> A ⇒ B ≡ (A ⇒ (IsTrue B)) 
⇒Classical3 {ℓ}{ℓ'} {A} {B} = compPath ⇒≡ (compPath (sym ⇒≡) (A≡BInA→C refl IsTrueClassical)) 

⇒Classical4 : {A : Type  ℓ} -> {B : Type  ℓ'} -> A ⇒ B ≡ ((IsTrue A) ⇒ (IsTrue B)) 
⇒Classical4 {ℓ}{ℓ'} {A} {B} = (compPath ⇒Classical2 ⇒Classical3)

-- "Implies" defined in terms of logical operators, that is, in terms of classical "Or"
A⇒B≡Or¬AB : {A : Type  ℓ} -> {B : Type  ℓ'} → (A ⇒ B) ≡ (Or (¬ A) B)
A⇒B≡Or¬AB {ℓ}{ℓ'} {A} {B}  = isoToPath (iso section' retract' (λ a → isPropOr (section' (retract' a)) a) (λ b → isProp⇒ (retract' (section' b)) b))
                                          where
                                            section' : A ⇒ B → Or (¬ A) B
                                            section' ab (x , y) = ab x y
                                            retract' : Or (¬ A) B → A ⇒ B
                                            retract' orab ist x = Or-absurd ist x orab

----
-- And a classical  double implication

_⟺_ : (A : Type ℓ) -> (B : Type ℓ') -> Type (ℓ-max ℓ ℓ') 
A ⟺ B = ((A ⇒ B) × (B ⇒ A))

isProp⟺ : {A : Type ℓ} -> {B : Type ℓ'} -> isProp (A ⟺ B)
isProp⟺ {ℓ} {ℓ'} {A} {B} (x , y) (w , z) = λ i → (isProp⇒ x w i , isProp⇒ y z i)

A⟺B≡IsTrueA⇒B×IsTrueB⇒A : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ((IsTrue (A ⇒ B)) × (IsTrue (B ⇒ A)))
A⟺B≡IsTrueA⇒B×IsTrueB⇒A {ℓ} {ℓ'} {A} {B} = A≡BInA×C ⇒Classical1 ⇒Classical1

A⟺B≡A⇒B×IsTrueB⇒A : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ((A ⇒ B) × (IsTrue (B ⇒ A)))
A⟺B≡A⇒B×IsTrueB⇒A {ℓ} {ℓ'} {A} {B} = A≡BInA×C refl ⇒Classical1

A⟺B≡IsTrueA⇒B×B⇒A : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ((IsTrue (A ⇒ B)) × (B ⇒ A))
A⟺B≡IsTrueA⇒B×B⇒A {ℓ} {ℓ'} {A} {B} = A≡BInA×C ⇒Classical1 refl

⟺Classical1-hlp : IsTrue ((IsTrue A) × (IsTrue B)) ≡ ((IsTrue A) × (IsTrue B))
⟺Classical1-hlp = NnnAandnB≡¬¬nnAornB 

⟺Classical1 : {A : Type ℓ} -> {B : Type ℓ'} -> A ⟺ B ≡ IsTrue (A ⟺ B)
⟺Classical1 {ℓ}{ℓ'} {A} {B} = compPath (compPath A⟺B≡IsTrueA⇒B×IsTrueB⇒A (sym ⟺Classical1-hlp)) (cong IsTrue (sym A⟺B≡IsTrueA⇒B×IsTrueB⇒A))

A⟺B≡IsTrueA'⇒B×B⇒A : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ( ((IsTrue A) ⇒ B) × (B ⇒ A) )
A⟺B≡IsTrueA'⇒B×B⇒A {ℓ}{ℓ'} {A} {B} = A≡BInA×C ⇒Classical2 refl

A⟺B≡A⇒IsTrueB'×B⇒A : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ( (A ⇒ (IsTrue B)) × (B ⇒ A) )
A⟺B≡A⇒IsTrueB'×B⇒A {ℓ}{ℓ'} {A} {B} = A≡BInA×C ⇒Classical3 refl

A⟺B≡A⇒B×IsTrueB'⇒A : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ( (A ⇒ B) × ((IsTrue B) ⇒ A) )
A⟺B≡A⇒B×IsTrueB'⇒A {ℓ}{ℓ'} {A} {B} = A≡BInA×C refl ⇒Classical2 

A⟺B≡A⇒B×B⇒IsTrueA : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ( (A ⇒ B) × (B ⇒ (IsTrue A)) )
A⟺B≡A⇒B×B⇒IsTrueA  {ℓ}{ℓ'}{A} {B} = A≡BInA×C refl ⇒Classical3

A⟺B≡A⇒B×B⇒IsTrueA' : {A : Type ℓ} -> {B : Type ℓ'} -> ((IsTrue A) ⇒ B) × (B ⇒ A) ≡ ((IsTrue A) ⇒ B) × ((B ⇒ (IsTrue A)))
A⟺B≡A⇒B×B⇒IsTrueA' {ℓ}{ℓ'} {A} {B} = A≡BInA×C refl ⇒Classical3

A⟺B≡IsTrueA'⇒B×B⇒IsTrueA : {A : Type ℓ} -> {B : Type ℓ'} -> (A ⟺ B) ≡ ( ((IsTrue A) ⇒ B) × (B ⇒ (IsTrue A)) )
A⟺B≡IsTrueA'⇒B×B⇒IsTrueA {ℓ} {ℓ'} {A} {B} = compPath A⟺B≡IsTrueA'⇒B×B⇒A A⟺B≡A⇒B×B⇒IsTrueA'

⟺Classical2 : {A : Type ℓ} -> {B : Type ℓ'} -> A ⟺ B ≡ (IsTrue A) ⟺ B
⟺Classical2 {ℓ}{ℓ'} {A} {B} = A⟺B≡IsTrueA'⇒B×B⇒IsTrueA 

⟺Classical3 : {A : Type ℓ} -> {B : Type ℓ'} -> A ⟺ B ≡ A ⟺ (IsTrue B)
⟺Classical3 {ℓ}{ℓ'} {A} {B} = compPath (compPath (swapEq ((x : (x₁ : (x₂ : A) → ⊥) → ⊥) (x₁ : (x₂ : B) → ⊥) → ⊥)
                                       ((x : (x₁ : (x₂ : B) → ⊥) → ⊥) (x₁ : (x₂ : A) → ⊥) → ⊥)) ⟺Classical2)
                                       (swapEq ((x : (x₁ : (x₂ : (x₃ : (x₄ : B) → ⊥) → ⊥) → ⊥) → ⊥)
                                                (x₁ : (x₂ : A) → ⊥) → ⊥) ((x : (x₁ : (x₂ : A) → ⊥) → ⊥)
                                                (x₁ : (x₂ : (x₃ : (x₄ : B) → ⊥) → ⊥) → ⊥) → ⊥))

⟺Classical4 : {A : Type ℓ} -> {B : Type ℓ'} -> A ⟺ B ≡ (IsTrue A) ⟺ (IsTrue B)
⟺Classical4 {ℓ}{ℓ'} {A} {B} = compPath ⟺Classical2 ⟺Classical3

----------------------------------------------
-- Modus Ponens and functions

-- A classical modus ponens 
ModusPonens⟹ : {A : Type ℓ} -> {B : Type ℓ'} -> (f : A ⇒ B) → (IsTrue A) → IsTrue B
ModusPonens⟹ {A = A}{B = B} f a = λ z → a (λ z₁ → f (λ z₂ → z₂ z₁) z)

ModusPonens⟹-classical : {A : Type ℓ} -> {B : Type ℓ'} -> A ⇒ (A ⇒ B) ⇒ B
ModusPonens⟹-classical  = λ z z₁ → z₁ (λ z₂ z₃ → z₂ (λ z₄ → z₄ z z₃))

WeakModusPonens⟹ : {A : Type ℓ} -> {B : Type ℓ'} -> (f : A ⇒ B) -> (a : A) -> IsTrue B
WeakModusPonens⟹ f a  = f (λ z → z a) 

WeakModusPonens⟹' : {A : Type ℓ} -> {B : Type ℓ'} -> (f : A → B) -> (IsTrue A) -> IsTrue B
WeakModusPonens⟹' f istA = λ z → istA (λ z₁ → z (f z₁)) 

ModusPonens-lemma : {A : Type ℓ} → {B : Type ℓ'} → (istA : IsTrue A) → (A ⇒ (B ⇒ C)) → B ⇒ C
ModusPonens-lemma = λ istA z z₁ z₂ → z₁ (λ z₃ → z istA (λ z₄ → z₄ (λ z₅ → z₅ z₃) z₂))

----
--Other useful functions and properties

A≡B→A⇒C→B⇒C :  {A B : Type  ℓ} → {C : Type  ℓ'} -> A ≡ B → A ⇒ C → B ⇒ C
A≡B→A⇒C→B⇒C {A = A} {B = B} {C = C} ab ac nnb = ModusPonens⟹ ac isTrueA
                                            where
                                              isTrueA≡isTrueB : (¬ ¬ A) ≡ (¬ ¬ B)
                                              isTrueA≡isTrueB = A≡B→¬¬A≡¬¬B ab
                                              isTrueA : IsTrue A
                                              isTrueA = transport (sym isTrueA≡isTrueB) nnb

IsTrueA→B→IsTrueA→IsTrueB : {A : Type ℓ} → {B : Type  ℓ'} → IsTrue (A → B) → IsTrue A → IsTrue B
IsTrueA→B→IsTrueA→IsTrueB  {ℓ}{ℓ'} {A} {B} = λ z z₁ z₂ → z₁ (λ z₃ → z (λ z₄ → z₂ (z₄ z₃)))

IsTrueA→IsTrueB→IstrueA→B : {A : Type ℓ} → {B : Type ℓ'} → IsTrue A → (IsTrue B → IsTrue (A → B))
IsTrueA→IsTrueB→IstrueA→B = λ _ z z₁ → z (λ z₂ → z₁ (λ _ → z₂))

¬A→B→A→¬B : {A : Type ℓ} → {B : Type ℓ'} → ¬ (A → B) → (A → ¬ B)
¬A→B→A→¬B = λ z _ z₁ → z (λ _ → z₁)

IsTrueA→B→A→IsTrueB-dep : {A : Type ℓ} → {B : A -> Type ℓ'} → (IsTrue ((a : A) → (B a))) → ((a : A) → IsTrue (B a))
IsTrueA→B→A→IsTrueB-dep = λ z a z₁ → z (λ z₂ → z₁ (z₂ a))  -- this is the basis of the classical universal quantifier (see below)

--¬A→B→A→¬B-dep : {A : Type ℓ} → {B : A -> Type ℓ'} → (a : A) -> (¬ ((a : A) → (B a))) → ¬ ¬ (Σ A (λ a -> ¬ (B a)))
--¬A→B→A→¬B-dep {A = A} {B = B} a  nx = λ x  → {!!}  °°°°° 

IsTrueA→B→A→IsTrueB-dep2' : {A : Type ℓ} → {B : A -> Type ℓ'} → {C :  Type ℓ''} → (IsTrue ((a : A) → ((B a) ⇒ C))) → ((a : A) → IsTrue ((B a) ⇒ C))
IsTrueA→B→A→IsTrueB-dep2' = IsTrueA→B→A→IsTrueB-dep

IsTrueA→A'→B→A→A'→IsTrueB-dep : {A : Type ℓ} →  {A' : Type ℓ'} → {B : A → A' → Type ℓ'} → (IsTrue ((a : A) → (a' : A') → (B a a'))) → ((a : A) → (a' : A') → IsTrue (B a a'))
IsTrueA→A'→B→A→A'→IsTrueB-dep = λ z a a' z₁ → z (λ z₂ → z₁ (z₂ a a'))  -- and similarly for two arguments

IsTrueA→B→IsTrueB→C→IsTrueA→C : {A : Type ℓ} → {B : Type  ℓ'}  → {C : Type  ℓ''} → IsTrue (A → B) → IsTrue (B → C) → IsTrue (A → C)
IsTrueA→B→IsTrueB→C→IsTrueA→C  {ℓ}{ℓ'} {ℓ''} {A} {B} A→B B→C = λ z → B→C (λ z₁ → A→B (λ z₂ → z (λ z₃ → z₁ (z₂ z₃))))

PushIsTrue : {A : Type ℓ} → {B : Type ℓ'} → A → IsTrue B → IsTrue (A × B)
PushIsTrue a istB = λ z → istB (λ z₁ → z (a , z₁))

PushIsTrue-dep : {A : Type ℓ} → {B : A -> Type ℓ'} → (a : A) → IsTrue (B a) → IsTrue (Σ A B)
PushIsTrue-dep a istB = λ z → istB (λ z₁ → z (a , z₁))

PushIsTrue-dep' : {A : Type ℓ} → {B : A -> Type ℓ'} → {C :  Type ℓ''} → (a : A) → IsTrue ((B a) → C) → IsTrue (Σ A (λ a → ((B a) → C)))
PushIsTrue-dep' a istB = λ z → istB (λ z₁ → z (a , z₁))

PushIsTrue-dep'' : {A : Type ℓ} → {B : A -> Type ℓ'} → {C :  Type ℓ''} → (Σ A (λ a → IsTrue ((B a) → C))) → IsTrue (Σ A (λ a → ((B a) → C)))
PushIsTrue-dep'' (x , y) = PushIsTrue-dep x y

PushIsTrue' : {A : Type ℓ} → {B : Type ℓ'} → IsTrue A → IsTrue B → IsTrue (A × B)
PushIsTrue' a istB = λ z → istB (λ z₁ → a (λ z₂ → z (z₂ , z₁)))

A→BIsTrueA→IsTrueB  : {A : Type ℓ} → {B : Type ℓ'} → (A → B) → (IsTrue A → IsTrue B)
A→BIsTrueA→IsTrueB {ℓ}{ℓ'}{A}{B} A→B IstA = λ z → IstA (λ z₁ → z (A→B z₁)) 

Decidablilty-IsTrueA→A  : {A : Type  ℓ} -> Dec A → ((IsTrue A) → A)
Decidablilty-IsTrueA→A {ℓ} {A} (yes p) nnA = p
Decidablilty-IsTrueA→A {ℓ} {A} (no ¬p) nnA = rec (IsTrue⊥ (λ z → z (nnA ¬p)))

Decidablilty-IsTrueIsTrueA→A  : {A : Type  ℓ} -> Dec A → ((IsTrue (IsTrue A)) → A)
Decidablilty-IsTrueIsTrueA→A {ℓ} {A} (yes p) hyp = p
Decidablilty-IsTrueIsTrueA→A {ℓ} {A} (no ¬p) hyp = rec (IsTrue⊥ (λ z → z (hyp (λ z₁ → z₁ ¬p))))

IsTrueIsTrueIsTrue-thm : {A : Type  ℓ} -> (IsTrue ( (IsTrue (IsTrue  A)) → A ))
IsTrueIsTrueIsTrue-thm {ℓ} {A} = A→BIsTrueA→IsTrueB Decidablilty-IsTrueIsTrueA→A (λ z → z (no (λ z₁ → z (yes z₁))))

Decidablilty-IsTrueA→A-dep  : {A : Type  ℓ} → {B : A -> Type ℓ'} -> Dec (∀ a -> (B a)) → IsTrue ((a : A) -> (B a)) → ((a : A) -> (B a))
Decidablilty-IsTrueA→A-dep {ℓ} {ℓ'} {A} {B} dc = Decidablilty-IsTrueA→A dc

IsTrueA→B→A→IsTrueB-dep-inv : {A : Type ℓ} → {B : A -> Type ℓ'} → (∀ a -> Dec (B a)) ->  ((a : A) → IsTrue (B a)) → ((a : A) → (B a))
IsTrueA→B→A→IsTrueB-dep-inv {ℓ} {ℓ'} {A} {B} dc ist a = Decidablilty-IsTrueA→A (dc a) (ist a)

IsTrueA→B→IsTrueB→A→IsTrueA≡B : {A B : Type ℓ} → IsTrue (A → B) → IsTrue (B → A) → IsTrue A ≡ IsTrue B
IsTrueA→B→IsTrueB→A→IsTrueA≡B  {ℓ} {A} {B} ab ba = isoToPath (iso (IsTrueA→B→IsTrueA→IsTrueB ab) (IsTrueA→B→IsTrueA→IsTrueB ba) (λ x -> isPropIsTrue (IsTrueA→B→IsTrueA→IsTrueB ab (IsTrueA→B→IsTrueA→IsTrueB ba x)) x) (λ x -> isPropIsTrue (IsTrueA→B→IsTrueA→IsTrueB ba (IsTrueA→B→IsTrueA→IsTrueB ab x)) x))



IsTrueDecA : {A : Type ℓ} → IsTrue (Dec A)
IsTrueDecA = λ z → z (no (λ z₁ → z (yes z₁)))

IsTrueIsTrueA→B'→IsTrueA→B  : {A : Type ℓ} → {B : Type ℓ'} → IsTrue ((IsTrue A) → B) → IsTrue (A → B) 
IsTrueIsTrueA→B'→IsTrueA→B ist  = λ z → ist (λ z₁ → z (λ z₂ → z₁ (λ z₃ → z₃ z₂)))

IsTrueIsTrueA→A : {A : Type ℓ} →  IsTrue (IsTrue A → A)
IsTrueIsTrueA→A {ℓ}{A} = IsTrueIsTrueA→B'→IsTrueA→B IsTrueIsTrueIsTrue-thm    

IsTrueA→IsTrueB'→IsTrueA→B  : {A : Type ℓ} → {B : Type  ℓ'} → (IsTrue A → IsTrue B) → IsTrue (A → B)
IsTrueA→IsTrueB'→IsTrueA→B  {ℓ}{ℓ'} {A} {B} x = IsTrueA→B→IsTrueB→C→IsTrueA→C lemma (IsTrueIsTrueA→A) 
                                                                        where
                                                                          lemma : IsTrue ((A) -> (IsTrue B))
                                                                          lemma = λ z → z (λ z₁ → x (λ z₂ → z₂ z₁))

A→isTrueB→istrueA→B : {A : Type ℓ} → {B : Type ℓ'} → (A → IsTrue B) → IsTrue (A → B)
A→isTrueB→istrueA→B  {ℓ} {ℓ'} {A} {B} AB = IsTrueA→B→IsTrueB→C→IsTrueA→C ist (IsTrueIsTrueA→B'→IsTrueA→B (IsTrueIsTrueIsTrue-thm) )
                                                    where
                                                      ist : IsTrue (A → IsTrue B)
                                                      ist = λ z → z AB
                                                      
isTrueA≡B→isTrueB≡C→isTrueA≡C : {A : Type ℓ} → {B : Type  ℓ} → {C : Type  ℓ} → IsTrue (A ≡ B) → IsTrue (B ≡ C) → IsTrue (A ≡ C)
isTrueA≡B→isTrueB≡C→isTrueA≡C  {ℓ} {A}{B}{C} AB BC =  IsTrueA→B→IsTrueA→IsTrueB (IsTrueA→B→IsTrueA→IsTrueB (pure compPath) AB) BC

isTrueA⟷B→isTrueA→B : {A : Type ℓ} → {B : Type ℓ'} → IsTrue (A ⟷ B) → IsTrue (A → B) 
isTrueA⟷B→isTrueA→B istAB = λ z → istAB (λ z₁ → z (_⟷_.AtoB z₁))

isTrueA⟷B→isTrueB→A : {A : Type ℓ} → {B : Type ℓ'} → IsTrue (A ⟷ B) → IsTrue (B → A) 
isTrueA⟷B→isTrueB→A istAB = λ z → istAB (λ z₁ → z (_⟷_.BtoA z₁))

isTrueA→B→isTrueB→A→isTrueA⟷B : {A : Type ℓ} → {B : Type ℓ'}  → IsTrue (A → B) → IsTrue (B → A) → IsTrue (A ⟷ B)
isTrueA→B→isTrueB→A→isTrueA⟷B atob btoa = λ z → btoa (λ z₁ → atob (λ z₂ → z (record { AtoB = z₂ ; BtoA = z₁ })))

IsTrue≡→IsTrue→ : {A : Type ℓ} → {B : Type ℓ} → IsTrue (A ≡ B) → IsTrue (A → B)
IsTrue≡→IsTrue→ =  WeakModusPonens⟹' (λ x x₁ → transport x x₁)

IsTrue≡→IsTrue→2 : {A : Type ℓ} → {B : Type ℓ} → IsTrue (A ≡ B) → IsTrue (B → A)
IsTrue≡→IsTrue→2 =  WeakModusPonens⟹' (λ x x₁ → transport (sym x) x₁)

IsTrue≡→IsTrue→' : {A : Type ℓ} → {B : Type ℓ} → IsTrue ((IsTrue A) ≡ (IsTrue B)) → ((IsTrue A) → (IsTrue B))
IsTrue≡→IsTrue→' ist = transport (sym ⇒Classical1) (IsTrue≡→IsTrue→ ist)

IsTrue≡→IsTrue→'2 : {A : Type ℓ} → {B : Type ℓ} → IsTrue ((IsTrue A) ≡ (IsTrue B)) → ((IsTrue B) → (IsTrue A))
IsTrue≡→IsTrue→'2 ist = transport (sym ⇒Classical1) (IsTrue≡→IsTrue→2 ist)

IsTrue≡→IsTrue≡ : {A : Type ℓ} → {B : Type ℓ} → IsTrue ((IsTrue A) ≡ (IsTrue B)) → ((IsTrue A) ≡ (IsTrue B))
IsTrue≡→IsTrue≡ ist = isoToPath (iso (IsTrue≡→IsTrue→' ist) (IsTrue≡→IsTrue→'2 ist) (λ x → isPropIsTrue (IsTrue≡→IsTrue→' ist (IsTrue≡→IsTrue→'2 ist x)) x ) (λ y → isPropIsTrue ( (IsTrue≡→IsTrue→'2 ist) ( (IsTrue≡→IsTrue→' ist) y) ) y))

isPropIsTrue≡IsTrue :  {A : Type ℓ} → {B : Type ℓ} → isProp ((IsTrue A) ≡ (IsTrue B))
isPropIsTrue≡IsTrue  = isProp⟷→isProp≡ isPropIsTrue isPropIsTrue

-- *
IsTrue≡'≡IsTrue≡ :  {A : Type ℓ} → {B : Type ℓ} → IsTrue ((IsTrue A) ≡ (IsTrue B)) ≡ ((IsTrue A) ≡ (IsTrue B))
IsTrue≡'≡IsTrue≡ {A = A} {B = B} = isoToPath (iso IsTrue≡→IsTrue≡ (A¬¬A) (λ x -> isPropIsTrue≡IsTrue (IsTrue≡→IsTrue≡ (A¬¬A x)) x) (λ y → isPropIsTrue (A¬¬A (IsTrue≡→IsTrue≡ y)) y))

----------------------------------------------
-- A note on classical versus constructive logic in terms of decidability and isProp propositions: 

ForallAB→∀AB : {A : Type ℓ} → {B : A → Type ℓ'} → (∀ (a : A) -> Dec (B a)) → Forall A B → ((a : A) → B a)
ForallAB→∀AB {ℓ} {ℓ'} {A} {B} dB fab a = Decidablilty-IsTrueA→A (dB a) (fab a)

PropDec→IsTrueA→B≡A→B-hlp : {A : Type ℓ} → {B : Type ℓ'} → Dec A → Dec B → (IsTrue (A → B)) → (A → B)
PropDec→IsTrueA→B≡A→B-hlp {ℓ} {ℓ'} {A} {B} da db ist = Decidablilty-IsTrueA→A (dec→ da db) ist

PropDec→IsTrueA→B≡A→B : {A : Type ℓ} → {B : Type ℓ'} → isProp B → Dec A → Dec B → (IsTrue (A → B)) ≡ (A → B) 
PropDec→IsTrueA→B≡A→B  {ℓ} {ℓ'} {A} {B} ispB da db = isoToPath (iso ( PropDec→IsTrueA→B≡A→B-hlp da db) pure (λ x → (isPropA→B ispB) (Decidablilty-IsTrueA→A (dec→ da db) (λ z → z x)) x) (λ y → isPropIsTrue (λ z → z (Decidablilty-IsTrueA→A (dec→ da db) y)) y))                                 

-- or without the cubical equality, thus without the isProp, but defining classical propositional equality to be double implication: 
DecADecB→IsTrueA→B≡A→B : {A : Type ℓ} → {B : Type ℓ'} → Dec A → Dec B → (IsTrue (A → B)) ⟷ (A → B) 
DecADecB→IsTrueA→B≡A→B  {ℓ} {ℓ'} {A} {B} da db = record { AtoB = PropDec→IsTrueA→B≡A→B-hlp da db ; BtoA = λ z z₁ → z₁ z }

Non-Falsifiability-EM : {A : Type  ℓ} -> (¬ ¬ ((¬ ¬ A) → A))
Non-Falsifiability-EM  {ℓ} {A} = A→B→¬¬A→¬¬B decP  (λ z → z (no (λ z₁ → z (yes z₁)))) 

---------------------------------------------
-- What is classical implication? The following are equivalences, which is very nice:

A⇒B=IsTrueA→IsTrueB : {A : Type ℓ} → {B : Type ℓ'} → (A ⇒ B) ≡ ((IsTrue A) → (IsTrue B))
A⇒B=IsTrueA→IsTrueB = refl  -- by definition

A⇒B=IsTrueA→IsTrueB-dep : {X : Type  ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → (x : X) → ((A x) ⇒ B) ≡ ((IsTrue (A x)) → (IsTrue B))
A⇒B=IsTrueA→IsTrueB-dep x = refl

A⇒B=IsTrueA→IsTrueB-dep' : {X : Type  ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → ((x : X) → ((A x) ⇒ B)) ≡ ((x : X) → (IsTrue (A x)) → (IsTrue B))
A⇒B=IsTrueA→IsTrueB-dep' = refl

IsTrueA→IsTrueAClassical :  {A : Type ℓ} → {B : Type ℓ'} → (IsTrue A → IsTrue B) ≡ IsTrue (IsTrue A → IsTrue B)
IsTrueA→IsTrueAClassical {ℓ}{ℓ'}{A} {B} = compPath (sym A⇒B=IsTrueA→IsTrueB) (compPath ⇒Classical1 refl)
                                              
IsTrueA→IsTrueB≡IstrueA→B : {A : Type ℓ} → {B : Type ℓ'} → ((IsTrue A) → (IsTrue B)) ≡ IsTrue (A → B)
IsTrueA→IsTrueB≡IstrueA→B  {ℓ} {ℓ'} {A} {B} = isoToPath (iso IsTrueA→IsTrueB'→IsTrueA→B IsTrueA→B→IsTrueA→IsTrueB (λ x → isPropIsTrue (IsTrueA→IsTrueB'→IsTrueA→B (IsTrueA→B→IsTrueA→IsTrueB x)) x) (λ y → isProp⇒ (IsTrueA→B→IsTrueA→IsTrueB (IsTrueA→IsTrueB'→IsTrueA→B y)) y))

IsTrueA→B→A≡IsTrueB-push : {A : Type ℓ} → {B : Type ℓ'} → (IsTrue (A → B)) ≡ (A → IsTrue B)
IsTrueA→B→A≡IsTrueB-push  {ℓ} {ℓ'} {A} {B} = isoToPath (iso IsTrueA→B→A→IsTrueB-dep A→isTrueB→istrueA→B (λ x → isPropForall (IsTrueA→B→A→IsTrueB-dep (A→isTrueB→istrueA→B x)) x) (λ y → isPropIsTrue (A→isTrueB→istrueA→B (IsTrueA→B→A→IsTrueB-dep y)) y))

-- Noting...
IsTrueA→B→A→IsTrueB-dep' : {A : Type ℓ} → {B : A -> Type ℓ'} → (IsTrue ((a : A) → (B a))) → ((a : A) → IsTrue (B a))  -- pushing the IsTrue through a ∀
IsTrueA→B→A→IsTrueB-dep'  {ℓ} {ℓ'} {A} {B} = IsTrueA→B→A→IsTrueB-dep        
-- (the IsTrue cannot in general be pulled out the other way...this in general has no inverse)

A⇒B=IsTrueA→B : {A : Type ℓ} → {B : Type ℓ'} → (A ⇒ B) ≡ (IsTrue (A → B))
A⇒B=IsTrueA→B = (compPath A⇒B=IsTrueA→IsTrueB IsTrueA→IsTrueB≡IstrueA→B)

x→IsTrueA→IsTrueB≡ : {X : Type ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → (Σ X (λ x → IsTrue (A x → B))) → IsTrue (Σ X (λ a → ((A a) → B)))
x→IsTrueA→IsTrueB≡  {X = X} {A = A} {B = B} = PushIsTrue-dep''

IsTrueA⇒B=IsTrueA→B : {A : Type ℓ} → {B : Type ℓ'} → (IsTrue (A ⇒ B)) ≡ (IsTrue (A → B))
IsTrueA⇒B=IsTrueA→B = compPath (sym ⇒Classical1) A⇒B=IsTrueA→B

A⇒B=IsTrueA→B-dep  : {X : Type  ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → (x : X) → ((A x) ⇒ B) ≡ (IsTrue ((A x) → B))
A⇒B=IsTrueA→B-dep x = A⇒B=IsTrueA→B

IsTrueA⇒B=IsTrueA→B-dep :  {X : Type  ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → (x : X) → (IsTrue ((A x) ⇒ B)) ≡ (IsTrue ((A x) → B))
IsTrueA⇒B=IsTrueA→B-dep x = compPath (sym ⇒Classical1) A⇒B=IsTrueA→B

uncurry-dep  : {X : Type  ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → (x : X) → ((A x) ⇒ B) → (Σ X (λ x -> (A x ⇒ B))) 
uncurry-dep {X = X} {A = A} {B = B} x AxB = x , (λ x x₁ → x (λ x₂ → AxB (λ z → z x₂) x₁))

specialise-dep : {X : Type  ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → ((x : X) → ((A x) → B)) → IsTrue X -> IsTrue (((x : X) -> A x) → B)
specialise-dep {X = X} {A = A} {B = B} xAxB istX  = λ z → istX (λ z₁ → z (λ z₂ → xAxB z₁ (z₂ z₁)))

specialise-dep' : {X : Type  ℓ} -> {A : X -> Type ℓ'} → {B : Type ℓ''} → ((x : X) → ((A x) ⇒ B)) → IsTrue X -> (((x : X) -> A x) ⇒ B)
specialise-dep' {X = X} {A = A} {B = B} xAxB istX  = λ z z₁ → z (λ z₂ → istX (λ z₃ → xAxB z₃ (λ z₄ → z₄ (z₂ z₃)) z₁))

C⇒A⇒B=IsTrueC→A→B : {A : Type ℓ} → {B : Type ℓ'} → {C : Type ℓ''}  → (C ⇒ (A ⇒ B)) ≡ (IsTrue (C → (A → B)))
C⇒A⇒B=IsTrueC→A→B = compPath (compPath A⇒B=IsTrueA→B (compPath IsTrueA→B→A≡IsTrueB-push (A→B≡A→C (compPath (sym ⇒Classical1) A⇒B=IsTrueA→B)))) (sym IsTrueA→B→A≡IsTrueB-push)

A⇒B=A→IsTrueB : {A : Type ℓ} → {B : Type ℓ'} → (A ⇒ B) ≡ (A → IsTrue B)
A⇒B=A→IsTrueB = compPath A⇒B=IsTrueA→B IsTrueA→B→A≡IsTrueB-push

A⇒B⇒C=A→B⇒C : {A : Type ℓ} → {B : Type ℓ'} → {C : Type ℓ''} → (A ⇒ (B ⇒ C)) ≡ (A → (B ⇒ C))
A⇒B⇒C=A→B⇒C {ℓ} {ℓ'} {ℓ''} {A}{B}{C} = compPath lemma lemma2
                   where
                     lemma2 : (A → IsTrue (B ⇒ C)) ≡ (A → (B ⇒ C))
                     lemma2 = cong (λ x → (A → x)) (sym  ⇒Classical1)
                     lemma : (A ⇒ (B ⇒ C)) ≡ (A → IsTrue (B ⇒ C))
                     lemma = A⇒B=A→IsTrueB

A⇒B⇒C=A→IsTrue'IsTrueB→IsTrueC : {A : Type ℓ} → {B : Type ℓ'}  → {B : Type ℓ''} → (A ⇒ (B ⇒ C)) ≡ (A → IsTrue ((IsTrue B) → (IsTrue C)))
A⇒B⇒C=A→IsTrue'IsTrueB→IsTrueC = compPath (compPath A⇒B=IsTrueA→IsTrueB IsTrueA→IsTrueB≡IstrueA→B) IsTrueA→B→A≡IsTrueB-push

----
-- Classical Currying

classical-curry-hlp : {A : Type ℓ} → {B : Type ℓ'} → {C : Type ℓ''} → (¬ ¬ (A × B)) → (A ⇒ (B ⇒ C)) → ¬ ¬ C
classical-curry-hlp {A = A} {B = B} {C = C} x y z = ModusPonens⟹ isTrueB⇒C isTrueB z
                                 where
                                   isTrueA : IsTrue A
                                   isTrueA = ¬¬AB→nnA x
                                   isTrueB : IsTrue B
                                   isTrueB = ¬¬AB→nnB x
                                   isTrueB⇒C : (B ⇒ C)
                                   isTrueB⇒C = ModusPonens-lemma isTrueA y
                                   
classical-curry : {A : Type ℓ} → {B : Type ℓ'} → {C : Type ℓ''} → (A ⇒ (B ⇒ C)) → ((A × B) ⇒ C)
classical-curry abc = λ x y → classical-curry-hlp x abc y

classical-uncurry : {A : Type ℓ} → {B : Type ℓ'} → {C : Type ℓ''} → ((A × B) ⇒ C) → (A ⇒ (B ⇒ C))
classical-uncurry = λ z z₁ z₂ → z₂ (λ z₃ z₄ → z₃ (λ z₅ → z₁ (λ z₆ → z (λ z₇ → z₇ (z₆ , z₅)) z₄)))

classical-uncurry2 : {A : Type ℓ} → {B : Type ℓ'} → {C : Type ℓ''} → (IsTrue ((A × B) ⇒ C)) → (A ⇒ (B ⇒ C))
classical-uncurry2 = λ z z₁ z₂ → z₂ (λ z₃ z₄ → z₃ (λ z₅ → z₁ (λ z₆ → z (λ z₇ → z₇ (λ z₈ → z₈ (z₆ , z₅)) z₄))))

-----------------------------------------------------
--Propositional Extensionality
-----------------------------------------------------

-- Note throughout that levels are required to be the same for comparisons of terms and types

isProp≡' : {A : Type ℓ} → (a b : A) → IsTrue (isProp A) → IsTrue (isProp (a ≡ b))
isProp≡' a b = A→B→¬¬A→¬¬B (isProp≡ a b)

propext-cl⟷1 : {A B : Type ℓ} → IsTrue (A → B) → IsTrue (B → A) → IsTrue (A ⟷ B)
propext-cl⟷1 {ℓ} {A} {B} istAB istBA = λ z → istBA (λ z₁ → istAB (λ z₂ → z (record { AtoB = z₂ ; BtoA = z₁ })))

propext-cl⟷2 : {A B : Type ℓ} → (IsTrue (A → B) × IsTrue (B → A)) → IsTrue (A ⟷ B)
propext-cl⟷2 {ℓ} {A} {B} (x , y) = propext-cl⟷1 (λ z → y (λ _ → x z)) y

propext-cl⟷3 : {A B : Type ℓ} → IsTrue (A ⟷ B) → (IsTrue (A → B) × IsTrue (B → A))
propext-cl⟷3 {ℓ} {A} {B} ist = (λ x → ist (λ z → x (_⟷_.AtoB z))) ,
                               (λ x → ist (λ z → x (_⟷_.BtoA z)))

-- A double implication-based classical version of propositional extensionality:
propext-cl⟷' : {A B : Type ℓ} → (IsTrue (A → B) × IsTrue (B → A)) ≡ IsTrue (A ⟷ B)
propext-cl⟷' {ℓ} {A} {B} = isoToPath (iso propext-cl⟷2 propext-cl⟷3 (λ x → isPropIsTrue (propext-cl⟷2 (propext-cl⟷3 x)) x) λ y → isPropNor (propext-cl⟷3 (propext-cl⟷2 y)) y)

propext-cl : {A B : Type ℓ} → isProp A → isProp B → IsTrue (A → B) → IsTrue (B → A) → IsTrue (A ≡ B)
propext-cl  {ℓ} {A} {B} pA pB istAB istBA =  WeakModusPonens⟹' (λ x → Props≡ pA pB (proj₂ (proj₂ x))) pushed 
                                            where
                                              pushed : IsTrue ((isProp A) × ((isProp B) × (A ⟷ B)))
                                              pushed = λ z → istBA (λ z₁ →
                                                    istAB (λ z₂ → z (pA , (pB , record { AtoB = z₂ ; BtoA = z₁ }))))

-- A classical propositional extensionality using cubical equality, with isTrue (isProp A) as the propositional criteria:
propext-cl' : {A B : Type ℓ} → IsTrue (isProp A) → IsTrue (isProp B) → IsTrue (A → B) → IsTrue (B → A) → IsTrue (A ≡ B)
propext-cl'  {ℓ} {A} {B} pA pB istAB istBA =  WeakModusPonens⟹' (λ x → Props≡ (proj₁ x) (proj₁ (proj₂ x)) (proj₂ (proj₂ x))) pushed 
                                            where
                                              pushed : IsTrue ( (isProp A) × ((isProp B) × (A ⟷ B)) )
                                              pushed = PushIsTrue' pA (λ z → istBA (λ z₁ → istAB
                                                                      (λ z₂ → pB (λ z₃ → z (z₃ , record { AtoB = z₂ ; BtoA = z₁ })))))

-- A fully classical propositional extensionality using cubical equality can be constructed another way:

pre-propExt-classical : {p q : Type  ℓ} → (IsTrue (p → q)) → (IsTrue (q → p)) → ((IsTrue p) ≡ (IsTrue q))
pre-propExt-classical pq qp = isoToPath (iso (λ z z₁ → z (λ z₂ → qp (λ _ → pq (λ z₃ → z₁ (z₃ z₂))))) (λ z z₁ → z (λ z₂ → qp (λ z₃ → z₁ (z₃ z₂))))
                                         (λ x → isPropIsTrue (λ z → x (λ z₁ → qp (λ z₂ → qp (λ _ → pq (λ z₃ → z (z₃ (z₂ z₁))))))) x)
                                          λ y → isPropIsTrue (λ z → y (λ z₁ → qp (λ _ → pq (λ z₂ → qp (λ z₃ → z (z₃ (z₂ z₁))))))) y)


pre-propExt-classical-uncurry : {p q : Type  ℓ} → ((IsTrue (p → q)) × (IsTrue (q → p))) → ((IsTrue p) ≡ (IsTrue q))
pre-propExt-classical-uncurry  pq = pre-propExt-classical (proj₁ pq) (proj₂ pq) 

-- with the following ensuring classicality of the final term:
propExt-classical : {p q : Type  ℓ} → (IsTrue (p → q)) → (IsTrue (q → p)) → IsTrue ((IsTrue p) ≡ (IsTrue q))
propExt-classical pq qp = A¬¬A (pre-propExt-classical pq qp)

-- This propositional equality (with its extensionality principle) can be expressed via an operator:

infix 6 _===_ 

-- A 'classical' Propositional equality...    
_===_ : (p q : Type ℓ) → Type (ℓ-suc ℓ)
_===_ p q = IsTrue ((IsTrue p) ≡ (IsTrue q))  

isProp=== : {p q : Type ℓ} → isProp (p === q)
isProp===  {ℓ}{p}{q} = isPropIsTrue

===Classical1 : {p q : Type ℓ} → (p === q) ≡ (IsTrue (p === q))  
===Classical1 = sym ¬¬¬A≡¬A 

-- The other classicality conditions also follow in a similar way.
-- And so we get a classical propositional extensionality expressed a bit more nicely (see propExt-classical-full):

propExt-classical-full-hlp : {A B : Type  ℓ} → (IsTrue ((B ⇒ A) → (A === B))) ≡ ((B ⇒ A) ⇒ (A === B))
propExt-classical-full-hlp = sym A⇒B=IsTrueA→B

propExt-classical-full-hlp3-hlp : {A B : Type  ℓ} →  (IsTrue ((A ⇒ B) → (B ⇒ A) → (A === B))) ≡  ((A ⇒ B) → ((B ⇒ A) → IsTrue (A === B)))
propExt-classical-full-hlp3-hlp {A = A} {B = B} = compPath IsTrueA→B→A≡IsTrueB-push (A→B≡A→C  IsTrueA→B→A≡IsTrueB-push)   

propExt-classical-full-hlp3 : {A B : Type  ℓ} →  (IsTrue ((A ⇒ B) → (B ⇒ A) → (A === B))) ≡  ((A ⇒ B) → (B ⇒ A) → (A === B))
propExt-classical-full-hlp3 = compPath propExt-classical-full-hlp3-hlp (A→B≡A→C (A→B≡A→C (sym ===Classical1)))

propExt-classical-full-hlp4 : {A B : Type  ℓ} → (IsTrue ((A ⇒ B) → (B ⇒ A) → (A === B))) ≡ ((A ⇒ B) ⇒ ((B ⇒ A) ⇒ (A === B)))
propExt-classical-full-hlp4 = sym C⇒A⇒B=IsTrueC→A→B

propExt-classical-full-hlp2 : {A B : Type  ℓ} → ((A ⇒ B) → (B ⇒ A) → (A === B)) ≡ ((A ⇒ B) ⇒ ((B ⇒ A) ⇒ (A === B)))
propExt-classical-full-hlp2 = compPath (sym propExt-classical-full-hlp3) propExt-classical-full-hlp4 

-- convenient version:
propExt-classical' : {A B : Type  ℓ} → (A ⇒ B) → (B ⇒ A) → (A === B)
propExt-classical' AB BA = propExt-classical (transport A⇒B=IsTrueA→B AB) (transport A⇒B=IsTrueA→B BA)

-- full version
propExt-classical-full : {A B : Type  ℓ} → (A ⇒ B) ⇒ ((B ⇒ A) ⇒ (A === B))
propExt-classical-full AB BA = transport propExt-classical-full-hlp2 propExt-classical' AB BA
                                                                      
-- We might consider all types to be propositions under _===_ as the defining equality.
-- This is in the spirit of 'types as propositions'; except here they are given a
-- 'classical' interpretation despite being Types.

-- An alternative version of classical propositional equality : _===_

infix 6 _==_ 

_==_ : (p q : Type ℓ) → Type (ℓ-suc ℓ)
_==_ p q = (IsTrue p) ≡ (IsTrue q)

p===q≣p==q :  (p q : Type ℓ) → (p === q) ≡ (p == q)
p===q≣p==q p q = IsTrue≡'≡IsTrue≡

----------------------------------------------
-- Developing Predicate Calculus
--   and using universal operators
----------------------------------------------

--Forall : (A : Type ℓ) -> (B : A → Type ℓ') -> Type (ℓ-max (ℓ) (ℓ')) 
--Forall A B = (x : A) → IsTrue (B x)

-- Note that the operators of propositional logic above cannot be applied
-- to predicate B (as used behind the universal quantifier here). The
-- reason is that  "¬ B", and similar constructions, do not type check.
-- Why? because these do not take the form "B : Type", but "B : A -> Type";
-- Meaning that the definition of ¬ does not pattern match on the
-- possible shape of B. That is, the usual notation of classical mathematics
-- is more polymorphic - in any case a 'not' can be formed for B, it is
-- just that it is a different function. This issue is why this is a 'First Attempt'.
-- It means there is extra overhead in coding this classical logic than is
-- preferable.

-- EXAMPLE OF CODE THAT IS AN EXTRA OVERHEAD

UnaryOn→ : {A : Type ℓ} → (unary : (Type ℓ' → Type ℓ'')) → (B : A → Type ℓ') → (A → Type ℓ'')
UnaryOn→ {ℓ} {ℓ'} {ℓ''} {A} unary B = λ x → unary (B x) 

-- IsTrue→ is analogous to an "IsTrue" applied to B : A → Type ℓ'  
IsTrueOn→  : {A : Type ℓ} → (B : A → Type ℓ') -> (A → Type ℓ')
IsTrueOn→  {ℓ} {ℓ'} {A} B = UnaryOn→ IsTrue B

IsTrueOn→'  : {A : Type ℓ} → (B : A → Type ℓ') -> (A → Type ℓ')
IsTrueOn→'  {ℓ} {ℓ'} {A} B = λ a → IsTrue (B a)

IsTrueOn→≡IsTrueOn→ : {A : Type ℓ} → (B : A → Type ℓ') -> (IsTrueOn→' B) ≡ (IsTrueOn→ B)
IsTrueOn→≡IsTrueOn→ B = refl

-- And the analog of ¬ ...
IsFalseOn→ : {A : Type ℓ} → (B : A → Type ℓ') -> (A → Type ℓ')  
IsFalseOn→  {ℓ} {ℓ'} {A} B = (UnaryOn→ IsFalse) B

-- But it gets worse...
IsTrueOn→→ : {A : Type ℓ} → {A' : Type ℓ'} → (B : A -> A' → Type ℓ'') -> (A → A' → Type ℓ'')
IsTrueOn→→  {ℓ} {ℓ'}{ℓ''}{A}{A'} B = λ a a' → IsTrue (B a a')

-- What we really want is for all this to de definable as something like:

-- IsTrue' : (B : Type' ℓ) -> Type' ℓ
-- IsTrue' (B : Type' ℓ) = ¬ ¬ B
-- IsTrue' (B : A -> Type' ℓ) = λ a ->  ¬ ¬ (B a)

-- So that: IsTrueOn→' and IsTrueOn→→  are all just covered by passing various arguments to IsTrue', that is, we want them to be the same function.

-- Exploring dependent arguments we reach similar problems:
IsTrueOn→dep : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : (a : A) -> (A' a) → Type ℓ'') -> ((a : A) → (A' a) → Type ℓ'')
IsTrueOn→dep  {ℓ} {ℓ'}{ℓ''}{A}{A'} B = λ a a' → IsTrue (B a a')

IsTrueOn→dep≡-info : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : (a : A) -> (A' a) → Type ℓ'') → (a : A) → (a' : A' a) → (IsTrueOn→dep B a a') ≡ IsTrue (B a a') 
IsTrueOn→dep≡-info  {ℓ} {ℓ'}{ℓ''}{A}{A'} B a a' = refl

IsTrueOn→dep≡ : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : (a : A) -> (A' a) → Type ℓ'') → (a : A) → (IsTrueOn→dep B a) ≡ IsTrueOn→ (B a) 
IsTrueOn→dep≡  {ℓ} {ℓ'}{ℓ''}{A}{A'} B a  = refl

-- and with the uncurried version likewise, but a little later:
IsTrueOn→dep' : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : (args : Σ A A') → Type ℓ'') → ((args' : Σ A A') → Type ℓ'')
IsTrueOn→dep'  {ℓ} {ℓ'}{ℓ''}{A}{A'} B = λ xy  → IsTrue (B xy)

IsTrueOn→dep'≡-info1 : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : (args : Σ A A') → Type ℓ'') → (args' : Σ A A') → (IsTrueOn→dep' B args') ≡ IsTrue (B args') 
IsTrueOn→dep'≡-info1  {ℓ} {ℓ'}{ℓ''}{A}{A'} B args = refl

IsTrueOn→dep'≡-info2 : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : (args : Σ A A') → Type ℓ'') →  (IsTrueOn→dep' B) ≡ IsTrueOn→ B 
IsTrueOn→dep'≡-info2  {ℓ} {ℓ'}{ℓ''}{A}{A'} B = refl

-- NB two cases not to be confused by:
IsTrueOn→dep-info1 : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : ((a : A) -> (A' a)) → Type ℓ'') -> (((a : A) -> (A' a)) → Type ℓ'')
IsTrueOn→dep-info1  {ℓ} {ℓ'}{ℓ''}{A}{A'} B = λ f → IsTrue (B f)  -- NB the f remains a dependent function type, eg instance of f ≡ Fin

IsTrueOn→dep-info2 : {A : Type ℓ} → {A' : A → Type ℓ'} → (B : (a : A) → ((a₀ : A) -> (A' a₀)) → Type ℓ'') → ((a' : A) → (f : (a₀' : A) → (A' a₀')) → Type ℓ'')
IsTrueOn→dep-info2  {ℓ} {ℓ'}{ℓ''}{A}{A'} B = λ a₀' f → IsTrue (B a₀' f) -- NB the f remains a function as it doesn't say (f : A' a₀') despite presence of a₀'

-------------------------------------------

ForallClassical1-info1 : {A : Type ℓ} → (B : A → Type ℓ') → IsTrue ((x : A) -> IsTrue (B x)) -> ((x : A) -> IsTrue (IsTrue (B x)))
ForallClassical1-info1 {ℓ} {ℓ'} {A} B ist  = λ x z → z (λ z₁ → ist (λ z₂ → z₂ x z₁))

ForallClassical1-info2 : {A : Type ℓ} → (B : A → Type ℓ') → ((x : A) -> IsTrue (IsTrue (B x))) -> ((x : A) -> (IsTrue (B x)))
ForallClassical1-info2 {ℓ} {ℓ'} {A} B ist  = λ x z → ist x (λ z₁ → z₁ z)

ForallClassical1-hlp : {A : Type ℓ} → {B : A → Type ℓ'} → IsTrue (Forall A B) -> Forall A B
ForallClassical1-hlp {ℓ} {ℓ'} {A} {B} ist  = λ x z → ist (λ z₁ → z₁ x z)

ForallClassical1 : {A : Type ℓ} → (B : A → Type ℓ') → Forall A B ≡ IsTrue (Forall A B)
ForallClassical1 {ℓ} {ℓ'} {A} B  = isoToPath (iso pure ForallClassical1-hlp (λ x -> isPropIsTrue (pure (ForallClassical1-hlp x)) x) λ y -> isPropForall (ForallClassical1-hlp (pure y)) y)

ForallClassical2-section : {A : Type ℓ} → {B : A → Type ℓ'} → Forall A B → (Forall A (λ x → IsTrue (B x))) 
ForallClassical2-section   {ℓ} {ℓ'} {A} {B} = λ z x z₁ → z₁ (z x)

ForallClassical2-retract : {A : Type ℓ} → {B : A → Type ℓ'} → (Forall A (λ x → IsTrue (B x))) → Forall A B 
ForallClassical2-retract   {ℓ} {ℓ'} {A} {B} = λ z x z₁ → z x (λ z₂ → z₂ z₁)

-- The following means that Forall (a : A) (B a) is equivalent to Forall (a : A) ("IsTrue'" B) a) and likewise "Forall A (IsTrueOn→ B)"
ForallClassical2 : {A : Type ℓ} → (B : A → Type ℓ') → Forall A B ≡ (Forall A (λ x → IsTrue (B x))) 
ForallClassical2 {ℓ} {ℓ'} {A} B = isoToPath (iso ForallClassical2-section ForallClassical2-retract (λ x -> isPropForall (ForallClassical2-section (ForallClassical2-retract x)) x) (λ y -> isPropForall (ForallClassical2-retract (ForallClassical2-section y)) y))

----

Forall¬ : (A : Type ℓ) -> (B : A → Type ℓ') -> Type (ℓ-max (ℓ) (ℓ')) 
Forall¬ A B = (x : A) → ¬ (B x)

isPropForalll¬-hlp : {A : Type ℓ} → {B : A → Type ℓ'} → isProp (∀ x → ¬ (B x))   
isPropForalll¬-hlp {ℓ} {ℓ'} {A} {B} = isProp-fun-dep (λ x → (isProp¬ _)) 

isPropForall¬ : {A : Type ℓ} -> {B : A → Type ℓ'} -> isProp (Forall¬ A B)
isPropForall¬ = isPropForalll¬-hlp

Forall¬→Forall'¬ :  {A : Type ℓ} -> {B : A → Type ℓ'} -> (Forall¬ A B) → Forall A (λ a -> ¬ (B a))   -- doubles up as 'classicality' condition for Forall¬
Forall¬→Forall'¬ fn  = λ x y → rec (y (fn x))

Forall'¬→Forall¬ :  {A : Type ℓ} -> {B : A → Type ℓ'} → Forall A (λ a -> ¬ (B a)) -> (Forall¬ A B)
Forall'¬→Forall¬ fn  = λ x z → fn x (λ z₁ → z₁ z)

Forall¬≡Forall'¬ :  {A : Type ℓ} -> {B : A → Type ℓ'} -> (Forall¬ A B) ≡ Forall A (λ a -> ¬ (B a)) -- this also shows Forall¬ is "classical"
Forall¬≡Forall'¬  = isoToPath (iso (Forall¬→Forall'¬) Forall'¬→Forall¬ (λ x → isPropForall (Forall¬→Forall'¬ (Forall'¬→Forall¬ x)) x) λ y → isPropForall¬ (λ x z → rec (y x z)) y)

Forall'¬≡Forall¬' :  {A : Type ℓ} -> {B : A → Type ℓ'} -> Forall¬ A (λ a → ¬ B a) ≡ Forall A B
Forall'¬≡Forall¬' =  refl

-----------------------------------------------
-- Classical Exists 
Exists : (A : Type ℓ) (B : A → Type ℓ') -> Type (ℓ-max (ℓ) (ℓ'))  
Exists A B =  IsTrue (Σ A B)

Extract : {A : Type ℓ} {B : A → Type ℓ'} -> Exists A B → IsTrue A
Extract = λ z z₁ → z (λ z₂ → z₁ (fst z₂))

ΣAB→∀A¬B→⊥ : {A : Type ℓ} {B : A → Type ℓ'} -> (Σ A B) → (∀ (x : A) → (¬ (B x))) → ⊥
ΣAB→∀A¬B→⊥ (fst1 , snd1) = λ z → z fst1 snd1

ΣAB→∀A¬B→⊥' : {A : Type ℓ} {B : A → Type ℓ'} -> (¬ ¬ (Σ A B)) → ¬ ¬ ((∀ (x : A) → (¬ (B x)))) → ¬ ¬ ⊥
ΣAB→∀A¬B→⊥' x y = IsTrueA→B→IsTrueA→IsTrueB (IsTrueA→B→IsTrueA→IsTrueB (A¬¬A ΣAB→∀A¬B→⊥) x) y

isPropExists :  (A : Type ℓ) -> (B : A → Type ℓ') -> isProp (Exists A B)
isPropExists {ℓ} {ℓ'} A B = isPropIsTrue 

¬Exists→Forall¬ : {A : Type ℓ} {B : A → Type ℓ'} -> (¬ (Exists A B)) → (Forall¬ A B)
¬Exists→Forall¬ {ℓ} {ℓ'} {A} {B} = λ z x z₁ → z (λ z₂ → z₂ (x , z₁))

Forall¬→¬Exists : {A : Type ℓ} {B : A → Type ℓ'}  → (Forall¬ A B) -> (¬ (Exists A B))
Forall¬→¬Exists {ℓ} {ℓ'} {A} {B} fa = λ x → ΣAB→∀A¬B→⊥' x (A¬¬A fa) (λ z → z)

¬Exists≡Forall¬ : (A : Type ℓ) (B : A → Type ℓ') -> (¬ (Exists A B)) ≡ (Forall¬ A B) 
¬Exists≡Forall¬ {ℓ} {ℓ'} A B = isoToPath (iso ¬Exists→Forall¬ Forall¬→¬Exists (λ x → isPropForall¬ x x) (λ y → isProp¬ _ (Forall¬→¬Exists (¬Exists→Forall¬ y)) y))

¬¬Exists≡¬Forall¬ : (A : Type ℓ) (B : A → Type ℓ') -> (¬ ¬ (Exists A B)) ≡ (¬ (Forall¬ A B)) 
¬¬Exists≡¬Forall¬ {ℓ} {ℓ'} A B = A≡B→¬A≡¬B (¬Exists≡Forall¬ A B)

ExistsClassical1 : (A : Type ℓ) -> (B : A → Type ℓ') -> Exists A B ≡ (IsTrue (Exists A B))
ExistsClassical1 {ℓ} {ℓ'} A B = IsTrueClassical

Exists≡¬Forall¬ : (A : Type ℓ) (B : A → Type ℓ') -> (Exists A B) ≡ (¬ (Forall¬ A B))  -- doubles up as "classicality" condition for Exists
Exists≡¬Forall¬ {ℓ} {ℓ'} A B = compPath (ExistsClassical1 A B) (¬¬Exists≡¬Forall¬ A B)

ExistsClassical2 : (A : Type ℓ) -> (B : A → Type ℓ') -> Exists A B ≡ (Exists A (λ a -> IsTrue (B a)))   -- (see idea for "IsTrue'" above, that would make this "IsTrue' B")
ExistsClassical2 {ℓ} {ℓ'} A B = compPath (compPath (Exists≡¬Forall¬ A B) (A≡B→¬A≡¬B Forall¬≡Forall'¬)) (sym (Exists≡¬Forall¬ _ _))

----

Exists¬ : (A : Type ℓ) (B : A → Type ℓ') -> Type (ℓ-max (ℓ) (ℓ'))  
Exists¬ A B =  ¬ ¬ (Σ A (λ a → ¬ (B a)))  

Exists¬≡ : {A : Type ℓ} {B : A → Type ℓ'} -> (Exists¬ A B) ≡ (Exists A (λ a -> ¬ (B a)))  -- doubles up as "classicality" condition for Exists¬
Exists¬≡ = refl 

Exists¬≡¬Forall : (A : Type ℓ) (B : A → Type ℓ') -> (Exists¬ A B) ≡ (¬ (Forall A B)) 
Exists¬≡¬Forall {ℓ} {ℓ'} A B = compPath (Exists≡¬Forall¬ A (λ z → (x : B z) → ⊥)) (cong (λ x → ¬ x) Forall'¬≡Forall¬')

IsTrueA→ForallA→ : {A : Type ℓ} {B : A → Type ℓ'} -> IsTrue A → Forall A B → Exists A B
IsTrueA→ForallA→  = λ z z₁ z₂ → z (λ z₃ → z₁ z₃ (λ z₄ → z₂ (z₃ , z₄)))

-------------------------------------------
-- The Usual Rules of Predicate Calculus
-------------------------------------------

--[Hilbert]	D. Hilbert, P. Bernays, "Grundlagen der Mathematik" , 1–2 , Springer (1934–1939)
--[Kleene]	S.C. Kleene, "Introduction to metamathematics" , North-Holland (1951)
--[Novikov]	P.S. Novikov, "Elements of mathematical logic" , Oliver & Boyd (1964) (Translated from Russian)
--[Takeuti]	G. Takeuti, "Proof theory" , North-Holland (1975)

-- In particular we now show the rules of propositional and predicate calculus as per [Kleene] section 19, page 82.
-- (Used automated proof search where possible).
-- Inference lines should be → rather than ⇒, but we shall see what this involves...

-- Group A1 Postulates for the propositional calculus.
rule-1a : {A : Type  ℓ} → {B : Type  ℓ'} -> A ⇒ (B ⇒ A)
rule-1a = λ z z₁ → z₁ (λ z₂ z₃ → z₂ (λ _ → z z₃))

rule-1b : {A : Type  ℓ} → {B : Type  ℓ'} → {C : Type  ℓ''} -> (A ⇒ B) ⇒ ((A ⇒ (B ⇒ C)) ⇒ (A ⇒ C))
rule-1b = λ z z₁ → z₁ (λ z₂ z₃ → z₃ (λ z₄ z₅ → z₄ (λ z₆ → z₂ (λ z₇ → z₇ (λ z₈ → z₈ z₆)
                      (λ z₈ → z₈ (λ z₉ → z (λ z₁₀ → z₁₀ (λ z₁₁ → z₁₁ z₆) z₉)) z₅)))))

rule-2 :  {A : Type  ℓ} → {B : Type  ℓ'} -> A ⇒ (A ⇒ B) ⇒ B
rule-2 = λ z z₁ → z₁ (λ z₂ z₃ → z₂ (λ z₄ → z₄ z z₃))

-- rule 2 is written in the format of natural deduction in Kleene, so the following is included here.
-- Note that the inference remains classical due to the ⇒
rule-2-uncurry :  {A : Type  ℓ} → {B : Type  ℓ'} -> (A × (A ⇒ B)) ⇒ B
rule-2-uncurry {ℓ} {ℓ'} {A} {B} = classical-curry ModusPonens⟹-classical  

rule-2-classicalB-hlp :  {A : Type  ℓ} → {B : Type  ℓ'} -> (A × (A ⇒ B)) → IsTrue B
rule-2-classicalB-hlp aab = λ x → proj₂ aab (A¬¬A (proj₁ aab)) x 

-- The following is that which best represents Kleene's rule-2. There is however an issue; we must
-- assume B is 'classical' (to the extent that 'B ≡ IsTrue B'). Rule-2 is therefore conditional
-- on as extra requirement to simply B being a Type:
rule-2-classicalB :  {A : Type  ℓ} → {B : Type  ℓ'} -> (B ≡ IsTrue B) → (A × (A ⇒ B)) → B
rule-2-classicalB B-classical aab = transport (sym B-classical) (rule-2-classicalB-hlp aab) 

rule-3 :  {A : Type  ℓ} → {B : Type  ℓ'} -> (A ⇒ (B ⇒ (And A B)))
rule-3 = λ z z₁ → z₁ (λ z₂ z₃ → z₃ (λ z₄ → z₄ ((λ x → z₂ (λ _ → z x)) , z₂)))

rule-4a-hlp : {A : Type  ℓ} → {B : Type  ℓ'} -> ((¬ ¬ A) × (¬ ¬ B)) ⇒ A
rule-4a-hlp {A = A} {B = B} = λ x y → ((¬¬¬A¬A (¬¬AB→nnA x)) y)

rule-4b-hlp : {A : Type  ℓ} → {B : Type  ℓ'} -> ((¬ ¬ A) × (¬ ¬ B)) ⇒ B
rule-4b-hlp {A = A} {B = B} = λ x y → ((¬¬¬A¬A (¬¬AB→nnB x)) y)

rule-4a : {A : Type  ℓ} → {B : Type  ℓ'} -> (And A B) ⇒ A
rule-4a {ℓ}{ℓ'} {A} {B} = A≡B→A⇒C→B⇒C (sym And≡¬¬A×¬¬B) rule-4a-hlp
                        
rule-4b : {A : Type  ℓ} → {B : Type  ℓ'} -> (And A B) ⇒ B
rule-4b  {ℓ}{ℓ'} {A} {B} =  A≡B→A⇒C→B⇒C (sym And≡¬¬A×¬¬B) rule-4b-hlp

rule-5a : {A : Type  ℓ} → {B : Type  ℓ'} → (A ⇒ (Or A B))
rule-5a {A = A} {B = B} = transport (sym A⇒B=IsTrueA→IsTrueB) λ a → A¬¬A (mkOr1 a)

rule-5b : {A : Type  ℓ} → {B : Type  ℓ'} → (B ⇒ (Or A B))
rule-5b =  transport (sym A⇒B=IsTrueA→IsTrueB) λ a → A¬¬A (mkOr2 a)

rule-6 : {A : Type  ℓ} → {B : Type  ℓ'} → {C : Type  ℓ''} -> (A ⇒ C) ⇒ ((B ⇒ C) ⇒ ((Or A B) ⇒ C))
rule-6 = λ z z₁ → z₁ (λ z₂ z₃ → z₃ (λ z₄ z₅ → z₄ (λ z₆ → z₆
                    ((λ x → z₂ (λ z₇ → z₇ (λ _ → z (λ z₈ → z₈ (λ z₉ → z₉ x) z₅)) z₅)) ,
                     (λ x → z₂ (λ z₇ → z₇ (λ z₈ → z₈ x) z₅))))))

rule-7 :  {A : Type  ℓ} → {B : Type  ℓ'} → (A ⇒ B) ⇒ ((A ⇒ (¬ B)) ⇒ (¬ A))
rule-7 = λ z z₁ → z₁ (λ z₂ z₃ → z₃ (λ z₄ → z₂ (λ z₅ →
                      z₅ (λ z₆ → z₆ z₄) (λ z₆ → z (λ z₇ → z₇ (λ z₈ → z₈ z₄) z₆)))))

rule-8 :  {A : Type  ℓ} → (¬ ¬ A) ⇒ A
rule-8 = λ z z₁ → z (λ z₂ → z₂ z₁)

-- Group A2 of [Kleene] (postulates of predicate calculus)
-- variables are 'free' and go in the 'context'. If there is an inference line, then variables
-- must go in the correct context, ie that on the left of the inference, or that on the right of the inference.
-- Here it is on the left...
rule-9 : (X : Type ℓ) -> (A : X → Type ℓ') -> (C : Type ℓ'') → (∀ (x : X) → (C ⇒ (A x))) → (C ⇒ (Forall X A))
rule-9 = λ X A C z z₁ z₂ → z₂ (λ x z₃ → z₁ (λ z₄ → z x (λ z₅ → z₅ z₄) z₃))

-- A variant where the variable x is not in the context as per the translation of Kleene's definition,
-- but it still works as x is not 'contained' in C:
rule-9' : (X : Type ℓ) -> (A : X → Type ℓ') -> (C : Type ℓ'') → (C ⇒ (∀ (x : X) → (A x))) → (C ⇒ (Forall X A))
rule-9' = λ X A C z z₁ z₂ →  z₂ (λ x z₃ → z₁ (λ z₄ → z (λ z₅ → z₅ z₄) (λ z₅ → z₃ (z₅ x))))

-- t is a variable which is "free for x in A(x)" [Kleene] (ie not contained in A or x). This means
-- Forall X A and A are not defined in terms of t. Despite t in the context, this is so.
-- (X and A are given prior t)
rule-10 : (X : Type ℓ) -> (A : X → Type ℓ') -> ∀ (t : X) → ((Forall X A) ⇒ (A t))
rule-10 = λ X A t z z₁ → z (λ z₂ → z₂ t z₁)

-- As with rule-10 t is not 'contained' in A or x, though of course there is no 'x' here as such; it
-- means that Exists X A is independent of t, which, despite t in the context, it is...
-- (X and A are given prior t)
rule-11 : (X : Type ℓ) -> (A : X → Type ℓ') -> ∀ (t : X) → ((A t) ⇒ (Exists X A))
rule-11 = λ X A t z z₁ → z₁ (λ z₂ → z (λ z₃ → z₂ (t , z₃)))

rule-12-hlp2 : {A : Type ℓ} -> {B : Type ℓ'} -> {C : Type ℓ''} → IsTrue A → IsTrue B → (A -> B -> C) -> IsTrue C
rule-12-hlp2 = λ z z₁ z₂ z₃ → z₁ (λ z₄ → z (λ z₅ → z₃ (z₂ z₅ z₄)))

rule-12-hlp2' : {A : Type ℓ} -> {B : Type ℓ'} -> {C : Type ℓ''} → IsTrue A → IsTrue B → (A -> B ⇒ C) ⇒ IsTrue C
rule-12-hlp2' = λ z z₁ z₂ z₃ → z₃ (λ z₄ → z₂ (λ z₅ → z₁ (λ z₆ → z (λ z₇ → z₅ z₇ (λ z₈ → z₈ z₆) z₄)))) 

rule-12-hlp2'' : {A : Type ℓ} -> {B : Type ℓ'} -> {C : Type ℓ''} → IsTrue A → IsTrue B → (A -> B ⇒ C) → IsTrue C
rule-12-hlp2'' = λ z z₁ z₂ z₃ → z₁ (λ z₄ → z (λ z₅ → z₂ z₅ (λ z₆ → z₆ z₄) z₃))

rule-12-hlp2''' : {A : Type ℓ} -> {B : Type ℓ'} -> {C : Type ℓ''} → IsTrue A → IsTrue B → (A ⇒ B ⇒ C) → IsTrue C
rule-12-hlp2''' = λ z z₁ z₂ z₃ → z₂ (λ z₄ → z₁ (λ _ → z z₄)) (λ z₄ → z₄ z₁ z₃)

rule-12-hlp3 :  (X : Type ℓ) -> (A : X → Type ℓ') -> (C : Type ℓ'') → (Σ X A) → (((x : X) → A x ⇒ C) ⇒ C)
rule-12-hlp3 X A C sig a =   IsTrueA→B→IsTrueA→IsTrueB lemma4 (λ z → z (snd sig))               
                                 where
                                   IsTruePushed :  (x : X) → IsTrue ((A x) ⇒  C)
                                   IsTruePushed = IsTrueA→B→A→IsTrueB-dep2' a 
                                   lemma2 : IsTrue ((A (fst sig)) ⇒ C)
                                   lemma2 = IsTruePushed (fst sig)
                                   lemma3 : (IsTrue ((A (fst sig)) ⇒ C)) ≡ (IsTrue ((A (fst sig)) → C))
                                   lemma3 = IsTrueA⇒B=IsTrueA→B-dep {X = X} {A = A} {B = C} (fst sig)
                                   lemma4 : IsTrue ((A (fst sig)) -> C)
                                   lemma4 = transport lemma3 lemma2  

-- 'x' is in the context of the hypothesis to the inference: 
rule-12 : (X : Type ℓ) -> (A : X → Type ℓ') -> (C : Type ℓ'') → (∀ (x : X) → ((A x) ⇒ C)) → ((Exists X A) ⇒ C)
rule-12 X A C Ax y = istC
                        where
                          existsXA : Exists X A
                          existsXA = transport (sym (ExistsClassical1 X A)) y
                          existsXAΣ : IsTrue (Σ X A)
                          existsXAΣ = existsXA
                          istxAC : IsTrue ((x : X) → A x ⇒ C)
                          istxAC = A¬¬A Ax
                          istC : IsTrue C
                          istC = rule-12-hlp2'' existsXAΣ istxAC (rule-12-hlp3 X A C)      


-------------------------------

-- The Famous Drinker Paradox of Smullyan:

-- proved by automated proof search using classical logic (p just means non-empty domain)
-- (levels included for full generality)
Drinker-paradox-classical : (P : Type ℓ) (p : P) (D : P → Type ℓ') →  Exists P (λ x → (D x) → (Forall P D))
Drinker-paradox-classical P p D = λ z → z (p , (λ x x₁ x₂ → z (x₁ , (λ x₃ x₄ x₅ → x₂ x₃))))

-- A more constructively expressed version (but is really the same as the above since ¬ Σ is equivalent to  ¬ Exists) using the existence quantifier equivalent:
Drinker-Σ :  (P : Type ℓ) (p : P) → ¬ Σ (P → Type ℓ') (λ D -> (¬ Σ P (λ x → (D x) → (Forall P D))))
Drinker-Σ P p (D , nEP) = nEP (p , (λ x x₁ x₂ → nEP (x₁ , (λ x₃ x₄ x₅ → x₂ x₃))))

--But notice that we have mixed and matched constructive and classical definitions in the preceding.
--This is perfectly OK, provided we are clear about each definition.
--A fully constructive version (not provable) can be described, just to show how the classical and constructive can be used alongside each other,
--albeit here only in an unprovable theorem:
--Drinker-constructive-Σ :  (P : Type ℓ) (p : P) → ¬ Σ (P → Type ℓ') (λ D -> (¬ Σ P (λ x → (D x) → (∀ (p : P) → (D p)))))
--Drinker-constructive-Σ P p (D , nEP) = {!!}

-- A theorem statement of a constructive version of the Drinker Paradox is valid in Agda as a statement to be proven, as a type, even if it is only a classical theorem and cannot be proven: 
Drinker-constructive-Σ-Type : {ℓ ℓ' : Level} ->  (P : Type ℓ) (p : P) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Drinker-constructive-Σ-Type  {ℓ} {ℓ'} P p  =  ¬ Σ (P → Type  ℓ') (λ D -> (¬ Σ P (λ x → (D x) → (∀ (p : P) → (D p)))))







