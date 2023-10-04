
{-# OPTIONS --safe #-}
{-# OPTIONS --no-main #-}
{-# OPTIONS --cubical #-}

module Cumulative-Experiment where

open import Level
open import Cubical.Foundations.Prelude hiding (Σ-syntax)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism  -- REMOVE no-eta-equality on ISO definition
open import Cubical.Foundations.Transport

open import Data.Product.Base
open import Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
-------------------------

EquivInv : {A : Type ℓ}{B : Type ℓ'} → A ≃ B → B → A
EquivInv (fs , sn) = (λ z → proj₁ (proj₁ (equiv-proof sn z)))

--equivProof' :  {A : Type ℓ}{B : Type ℓ'} → (f : A ≃ B) → (y : B) → isContr (fiber (fst f) y)   -- to make this work remove 'no-eta-equality' from isEquiv 
--equivProof' (fs , record { equiv-proof = equiv-proof }) = equiv-proof

isoToEquivEquivToIso≡Id : {A : Type ℓ}{B : Type ℓ'} → ∀ (x : A ≃ B) → (isoToEquiv (equivToIso x)) ≡ x
isoToEquivEquivToIso≡Id  x  = equivEq refl

invEquivInvEquiv≡Id : {A : Type ℓ}{B : Type ℓ'} → ∀ (x : A ≃ B) → (invEquiv (invEquiv x)) ≡ x
invEquivInvEquiv≡Id  x = equivEq refl

invIsoInvIso≡Id : {A : Type ℓ}{B : Type ℓ'} → ∀ (x : Iso A B) → (invIso (invIso x)) ≡ x
invIsoInvIso≡Id x = refl

isoToEquivEquivToIsoTo≡ :  {A : Type ℓ}{B : Type ℓ'} → ∀ (x y : A ≃ B) → (isoToEquiv (equivToIso x)) ≡ (isoToEquiv (equivToIso y)) → x ≡ y 
isoToEquivEquivToIsoTo≡ x y eq = sym (isoToEquivEquivToIso≡Id x) ∙ eq ∙ (isoToEquivEquivToIso≡Id y)

invEquivIsoToEquiv≡ :  {A : Type ℓ}{B : Type ℓ'} → ∀ (x : Iso A B) → invEquiv (isoToEquiv x) ≡ isoToEquiv (invIso x)
invEquivIsoToEquiv≡ x = equivEq refl

invEquivIsoToEquiv≡2 :  {A : Type ℓ}{B : Type ℓ'} → ∀ (x : Iso A B) → (invEquiv (invEquiv (isoToEquiv x))) ≡ (isoToEquiv (invIso (invIso x)))
invEquivIsoToEquiv≡2 x = equivEq refl

isoToEquivInvIsoEquivToIso :  {F : Type ℓ}{G : Type ℓ'} →  (FG : F ≃ G) ->  isoToEquiv (invIso (equivToIso FG)) ≡ invEquiv FG
isoToEquivInvIsoEquivToIso FG = refl

-- Equivalence is taken as the basis for defining a cumulative equality on Types.
refl≃ : {F : Type ℓ} → F ≃ F
refl≃ {F = F} = idEquiv F 

sym≃ : {F : Type ℓ}{G : Type ℓ'} → F ≃ G → G ≃ F
sym≃ {F = F} {G = G} FG = invEquiv FG

sym¬≃  : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → ¬ (F ≃ G) → ¬ (G ≃ F)
sym¬≃ nfg' = λ x → nfg' (sym≃ x)

Sym≃-id-section : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → section (sym≃ {ℓ = ℓ} {ℓ' = ℓ'}{F = F}{G = G}) (sym≃ {ℓ = ℓ'} {ℓ' = ℓ})
Sym≃-id-section GF = invEquivInvEquiv≡Id GF

trans≃ : {A : Type ℓ}{B : Type ℓ'}{C : Type ℓ''} → A ≃ B → B ≃ C → A ≃ C
trans≃ = compEquiv   

transport≃ : {A : Type ℓ}{B : Type ℓ'} → A ≃ B → A → B
transport≃ = equivFun

transport⁻≃ : ∀ {ℓ} {ℓ'}{A : Type ℓ}{B : Type ℓ'} → A ≃ B → B → A
transport⁻≃ p = invEq p 

transport⁻≃' : {A : Type ℓ}{B : Type ℓ'} → A ≃ B → B → A
transport⁻≃' AB b = transport≃ (sym≃ AB) b

transport⁻≃'≡transport⁻≃ :  {A : Type ℓ}{B : Type ℓ'} → (AB : A ≃ B) → (b : B) →  transport⁻≃' AB b ≡ transport⁻≃ AB b
transport⁻≃'≡transport⁻≃ {A = A} {B = B} AB b = refl

-- The Type that two elements are the 'same' under an equivalence of their Types
≃-Elem : ∀ {ℓ}{ℓ'}{A : Set ℓ} -> {B : Set ℓ'} → (A ≃ B) -> (a : A) -> (b : B) -> Type ℓ'
≃-Elem AB a b = transport≃ AB a ≡ b

transport≃-id : {A : Type ℓ}{B : Type ℓ'} → (AB : A ≃ B) → (a : A) → (b : B) → (≃-Elem AB a b) ≡ (transport≃ AB a ≡ b) 
transport≃-id AB a b = refl

transport≃→id : {A : Type ℓ}{B : Type ℓ'} → (AB : A ≃ B) → {a : A} → {b : B} → (≃-Elem AB a b) → (transport≃ AB a ≡ b) 
transport≃→id AB {a = a} {b = b} elm  = transport (transport≃-id AB a b) elm  

predTransport≃ : {A : Type ℓ}{B : Type ℓ'} → A ≃ B → (fnA : A → Type ℓ'' ) → (B → Type ℓ'')
predTransport≃ AB fnA b = fnA (transport⁻≃ AB b)

predTransport⁻≃ : {A : Type ℓ}{B : Type ℓ'} → A ≃ B → (fnB : B → Type ℓ'') → (A → Type ℓ'')
predTransport⁻≃ AB fnB a = fnB (transport≃ AB a) 

--------------------------------------------------
infix 4 _≡≡_
-- A 'cumulative' equality of 'Type's:
_≡≡_ : ∀ {ℓ} {ℓ'} (F : Set ℓ) -> (G : Set ℓ') → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))  
_≡≡_  {ℓ = ℓ} {ℓ' = ℓ'} F G = (Level.Lift {ℓ} (ℓ') F) ≡ (Level.Lift {ℓ'} (ℓ) G)

≡≡-id :  ∀ {ℓ} {ℓ'} (F : Set ℓ) -> (G : Set ℓ') →  (F ≡≡ G) ≡ ((Level.Lift  {ℓ} (ℓ') F) ≡ (Level.Lift {ℓ'} (ℓ) G))
≡≡-id F G = refl

---

Lift≃ : ∀ {ℓ ℓ'} {A : Type ℓ} → Level.Lift ℓ' A ≃ A
Lift≃ .fst = Level.lower
Lift≃ .snd .equiv-proof = strictContrFibers Level.lift

Lift≃' : ∀ {ℓ ℓ'} {A : Type ℓ} → A ≃ (Level.Lift ℓ' A)
proj₁ Lift≃' = lift
snd Lift≃' = record { equiv-proof = strictContrFibers (λ z → lower z) }

≡≡→Equiv : ∀ {ℓ} {ℓ'} {A : Set ℓ} -> {B : Set ℓ'} → (A ≡≡ B) → (A ≃ B)
≡≡→Equiv {ℓ}{ℓ'}{A}{B} p = Lift≃' ∙ₑ (pathToEquiv p)  ∙ₑ  Lift≃                   
                  
Equiv→≡≡ : ∀ {ℓ} {ℓ'} {A : Set ℓ} -> {B : Set ℓ'} → (A ≃ B) → (A ≡≡ B)
Equiv→≡≡ {ℓ}{ℓ'}{A}{B} e =  ua (Lift≃ ∙ₑ e ∙ₑ Lift≃') 

trans-≡≡ : ∀ {ℓ} {ℓ'} {ℓ''} {F : Type ℓ} {G : Type ℓ'} {H : Type ℓ''} → F ≡≡ G → G ≡≡ H → F ≡≡ H
trans-≡≡ FG GH = Equiv→≡≡ (≡≡→Equiv FG ∙ₑ ≡≡→Equiv GH)

invEquiv' :  ∀ {ℓ} {ℓ'} {A : Set ℓ} -> {B : Set ℓ'} → A ≃ B → B ≃ A
invEquiv' {ℓ}{ℓ'}{A}{B} e = ≡≡→Equiv (sym (Equiv→≡≡ e))  

invEquiv'' :  ∀ {ℓ} {ℓ'} {A : Set ℓ} -> {B : Set ℓ'} → A ≃ B → B ≃ A  
invEquiv''  {ℓ}{ℓ'}{A}{B} e =  Lift≃' {ℓ'}{ℓ}{B} ∙ₑ (pathToEquiv (sym  (ua (Lift≃ {ℓ}{ℓ'}{A} ∙ₑ e ∙ₑ Lift≃')))) ∙ₑ Lift≃  

---
≡≡→≃ : ∀ {ℓ ℓ'} {F : Type ℓ} {G : Type ℓ'} → F ≡≡ G → F ≃ G
≡≡→≃ p = invEquiv Lift≃ ∙ₑ pathToEquiv p ∙ₑ Lift≃

≃→≡≡ : ∀ {ℓ ℓ'} {F : Type ℓ} {G : Type ℓ'} → F ≃ G → F ≡≡ G
≃→≡≡ e = ua (Lift≃ ∙ₑ e ∙ₑ invEquiv Lift≃)

-- Proof thanks to Agda Zulip group:
trans≡≡ : ∀ {ℓ} {ℓ'} {ℓ''} {F : Type ℓ} {G : Type ℓ'} {H : Type ℓ''} → F ≡≡ G → G ≡≡ H → F ≡≡ H
trans≡≡ FG GH = ≃→≡≡ (≡≡→≃ FG ∙ₑ ≡≡→≃ GH)

trans≡≡-id : ∀ {ℓ ℓ' ℓ''} {F : Type ℓ} {G : Type ℓ'} {H : Type ℓ''} {FG : F ≡≡ G}{GH : G ≡≡ H}{FH : F ≡≡ H} → (trans≡≡ FG GH) ≡ ≃→≡≡ ((≡≡→≃ FG) ∙ₑ (≡≡→≃ GH)) 
trans≡≡-id = refl

Lift≃Equiv : ∀ {ℓ ℓ'} {F : Type ℓ} {G : Type ℓ'} → ((Level.Lift ℓ' F) ≃ (Level.Lift ℓ G)) ≃ (F ≃ G) 
Lift≃Equiv = equivComp Lift≃ Lift≃

univalence≡≡-hlp : ∀ {ℓ} {ℓ'} (F : Set ℓ) -> (G : Set ℓ') →  (F ≡≡ G) ≃ ((Level.Lift  {ℓ} (ℓ') F) ≃ (Level.Lift {ℓ'} (ℓ) G))
univalence≡≡-hlp {ℓ}{ℓ'} F G = compEquiv (pathToEquiv (≡≡-id F G)) ua-step
          where
             ua-step : ((Level.Lift  {ℓ} (ℓ') F) ≡ (Level.Lift {ℓ'} (ℓ) G)) ≃ ((Level.Lift  {ℓ} (ℓ') F) ≃ (Level.Lift {ℓ'} (ℓ) G))
             ua-step = univalence

univalence≡≡ : {F : Type ℓ}{G : Type ℓ'} → (F ≡≡ G) ≃ (F ≃ G)
univalence≡≡ {ℓ}{ℓ'}{F}{G} = compEquiv (univalence≡≡-hlp F G) Lift≃Equiv

{-- THIS DOESN'T WORK, but it might be interesting that it doesn't:
univalenceIso' : {F : Type ℓ}{G : Type ℓ'} → (Iso F G) ≃ (F ≃ G)
univalenceIso' {ℓ}{ℓ'}{F}{G} = (λ x → step1 x) , step2 (iso step1 step3 step4 {!!})
            where
              step1 :  (Iso F G) → (F ≃ G)
              step1 = isoToEquiv
              step2 : (iso' : Iso (Iso F G) (F ≃ G)) → isEquiv (Iso.fun iso')
              step2 = isoToIsEquiv
              step3 :  (F ≃ G) → (Iso F G)
              step3 FG = equivToIso FG
              step4 : section step1 step3
              step4 = λ b → isoToEquivEquivToIso≡Id b
              step5 : retract step1 step3
              step5 = sect31
                 where
                   sect31 : section step3 step1
                   sect31 = λ b → {!!} -}
             
LiftEquivs : ∀ {F : Type ℓ}{G : Type ℓ'} →  (Level.Lift ℓ' F ≃ Level.Lift ℓ G) ≃ Level.Lift (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (F ≃ G)
LiftEquivs = Lift≃Equiv  ∙ₑ invEquiv Lift≃

univalencePath≡≡-hlp : {F : Type ℓ}{G : Type ℓ'} → (F ≡≡ G) ≃ Level.Lift (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (F ≃ G)
univalencePath≡≡-hlp = compEquiv univalence LiftEquivs

univalencePath≡≡ :  {F : Type ℓ}{G : Type ℓ'} → (F ≡≡ G) ≡ Level.Lift _ (F ≃ G)
univalencePath≡≡ = ua univalencePath≡≡-hlp

transport≡≡ : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → F ≡≡ G → F → G
transport≡≡ {ℓ} {ℓ'} FG myF = lower (transport FG (Level.lift myF))

transport⁻≡≡ : ∀ {ℓ}{ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → F ≡≡ G → G → F
transport⁻≡≡ {ℓ}{ℓ'} FG g = lower (transport (sym FG) (Level.lift g))

transport⁻Transport≡≡ : ∀ {ℓ}{ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (FG : F ≡≡ G) → (f : F) → (transport⁻≡≡ FG (transport≡≡ FG f)) ≡ f
transport⁻Transport≡≡ {F = F} {G = G} FG f = cong lower (transport⁻Transport FG (Level.lift f))

transportTransport⁻≡≡ : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (FG : F ≡≡ G) → (g : G) → (transport≡≡ FG (transport⁻≡≡ FG g)) ≡ g
transportTransport⁻≡≡ {F = F} {G = G} FG g = cong lower (transportTransport⁻ FG (Level.lift g))

--invEquiv1 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) -> isEquiv f → B → A  -- to make this work remove 'no-eta-equality' from isEquiv
--invEquiv1 {ℓ} {ℓ'} {A} {B} f record { equiv-proof = equiv-proof } = λ z → fst (fst (equiv-proof z))

≡≡→Iso : ∀ {ℓ ℓ'} {F : Type ℓ} {G : Type ℓ'} → F ≡≡ G → Iso F G
≡≡→Iso FG = iso (transport≡≡ FG) (transport⁻≡≡ FG) (transportTransport⁻≡≡ FG) (transport⁻Transport≡≡ FG)

-- Longer proof of trans of ≡≡
step1f : ∀ {ℓ}{ℓ''}{ℓ'} (F : Set ℓ) → (Level.Lift {ℓ} (ℓ'') F) -> (Level.Lift {ℓ} (ℓ') F)
step1f {ℓ}{ℓ''}{ℓ'} F =  λ z → Level.lift {a = ℓ} (lower {a = ℓ} z)

step2f :  ∀ {ℓ}{ℓ'} {F : Set ℓ} → {G : Set ℓ'} → (FG : F ≡≡ G) -> (Level.Lift {ℓ} (ℓ') F) -> (Level.Lift {ℓ'} (ℓ) G)
step2f  {ℓ}{ℓ'} FG b = transport FG b

transf :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} → F ≡≡ G → G ≡≡ H →  (Level.Lift  {ℓ} (ℓ'') F) ->  (Level.Lift  {ℓ''} (ℓ) H)
transf  {ℓ} {ℓ'} {ℓ''} {F = F} {G = G} {H = H} FG GH x = step1f H (step2f GH (step1f G (step2f FG (step1f F x))))         
                            
transg :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> F ≡≡ G → G ≡≡ H → (Level.Lift  {ℓ''} (ℓ) H) ->  (Level.Lift  {ℓ} (ℓ'') F)
transg  {ℓ} {ℓ'} {ℓ''} {F = F} {G = G} {H = H} FG GH lf = step1f F (step2f (sym FG) (step1f G (step2f (sym GH) (step1f H lf))))         

transf-id :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) → (x : Level.Lift {ℓ} (ℓ'') F) -> transf FG GH x ≡  step1f H (step2f GH (step1f G (step2f FG (step1f F x))))
transf-id FG GH x = refl

transg-id :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) → (x : Level.Lift  {ℓ''} (ℓ) H) -> transg FG GH x ≡ step1f F (step2f (sym FG) (step1f G (step2f (sym GH) (step1f H x))))
transg-id FG GH x = refl

transfg1 :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> ∀ x → transf FG GH (transg FG GH x) ≡   step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G (step2f {ℓ = ℓ} {ℓ' = ℓ'} FG
          (step1f {ℓ = ℓ} {ℓ'' = ℓ''} {ℓ' = ℓ'} F
          (step1f {ℓ = ℓ} {ℓ'' = ℓ'} {ℓ' = ℓ''} F (step2f {ℓ = ℓ'} {ℓ' = ℓ} (sym FG)
          (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x ))))))))) 
transfg1 {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = refl

transfg2 :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> ∀ x → transf FG GH (transg FG GH x) ≡   step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G (step2f {ℓ = ℓ} {ℓ' = ℓ'} FG
          (step2f {ℓ = ℓ'} {ℓ' = ℓ} (sym FG)
          (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x ))))))) 
transfg2 {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = refl

transfg3-hlp : ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'}  → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> (x : Level.Lift ℓ G) → (step2f {ℓ = ℓ} {ℓ' = ℓ'} FG (step2f {ℓ = ℓ'} {ℓ' = ℓ} (sym FG) x)) ≡ x
transfg3-hlp {ℓ}{ℓ'}{ℓ''}{F}{G}{H} FG GH x = (transport⁻Transport {ℓ = ℓ-max ℓ ℓ'} {A =  Level.Lift ℓ G} {B =  Level.Lift ℓ' F} (sym FG) x)

transfg3 :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> (x : Level.Lift ℓ H)  →
          (step2f {ℓ = ℓ} {ℓ' = ℓ'} FG (step2f {ℓ = ℓ'} {ℓ' = ℓ} (sym FG)
           (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
           (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))))
          ≡ 
           (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
           (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))
transfg3 {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = transfg3-hlp {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''}{F = F} {G = G} {H = H} FG GH
           (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH) (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))

transfg4 :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> (x : Level.Lift ℓ H) →
          step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G
          (step2f {ℓ = ℓ} {ℓ' = ℓ'} FG (step2f {ℓ = ℓ'} {ℓ' = ℓ} (sym FG)
          (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))))))
          ≡
          step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G
          (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))))
transfg4 {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = cong (myfn x) (transfg3 FG GH x)
           where
             test : (x : Level.Lift ℓ H) → Level.Lift ℓ G
             test =  λ (x' : Level.Lift ℓ H) -> (step1f {ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
                     (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x' )))
             test2 : (y' : Level.Lift ℓ H) → Level.Lift ℓ H
             test2 =  λ (y' : Level.Lift ℓ H)  -> step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
                      (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G
                      (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
                      (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H y' )))))
             test3 : (x : Level.Lift ℓ G) → Level.Lift ℓ H         
             test3 =  λ (z' : Level.Lift ℓ G)  -> step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
                      (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G z'))
             myfn : Level.Lift ℓ H -> Level.Lift ℓ G ->  Level.Lift ℓ H
             myfn w' tyG-lifted  = test3 tyG-lifted

transfg5 :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> ∀ x → transf FG GH (transg FG GH x) ≡   step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G
          (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))))
transfg5 {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = (transfg2 FG GH x ∙ transfg4 FG GH x)         

transfg6-hlp : ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'}  → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> (x : Level.Lift ℓ'' G) →  (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G x)) ≡ x
transfg6-hlp {ℓ}{ℓ'}{ℓ''}{F}{G}{H} FG GH x = refl

transfg6 :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> (x : Level.Lift ℓ H)  →
          (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G
          (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))
           ≡
          (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))
transfg6 {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = transfg6-hlp FG GH (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH) (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x ))

transfg7 :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> (x : Level.Lift ℓ H) ->
          step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step1f {ℓ = ℓ'} {ℓ'' = ℓ} {ℓ' = ℓ''} G
          (step1f{ℓ = ℓ'} {ℓ'' = ℓ''} {ℓ' = ℓ} G (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))))
          ≡
          step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))
transfg7 {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = cong (myfn x) (transfg6 FG GH x) 
            where
               test : Level.Lift ℓ H -> Level.Lift ℓ'' G
               test =  λ x' -> (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH) (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x'))
               test2 : Level.Lift ℓ H -> Level.Lift ℓ H
               test2 =  λ y' -> step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
                        (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH) (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H y' )))
               test3 : Level.Lift ℓ'' G -> Level.Lift ℓ H
               test3 =  λ y' -> step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH y')
               myfn :  Level.Lift ℓ H ->  Level.Lift ℓ'' G ->  Level.Lift ℓ H
               myfn w' tyG =  test3 tyG

transfg8 :  ∀ {ℓ} {ℓ'} {ℓ''} → {G : Set ℓ'} → {H :  Set ℓ''} → (GH : G ≡≡ H) -> (x : Level.Lift ℓ H) ->
          (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))
           ≡ 
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )
transfg8 {ℓ} {ℓ'} {ℓ''}{G}{H} GH x = transfg3-hlp GH (sym GH) (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x)

transfg9 :  ∀ {ℓ} {ℓ'} {ℓ''} → {G : Set ℓ'} → {H :  Set ℓ''} → (GH : G ≡≡ H) -> (x : Level.Lift ℓ H) ->
          step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H
          (step2f {ℓ = ℓ'} {ℓ' = ℓ''} GH
          (step2f {ℓ = ℓ''} {ℓ' = ℓ'} (sym GH)
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )))
           ≡
          step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H 
          (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x )
transfg9 {ℓ} {ℓ'} {ℓ''}{G}{H} GH x = cong (myfn x) (transfg3-hlp GH (sym GH) (step1f{ℓ = ℓ''} {ℓ'' = ℓ} {ℓ' = ℓ'} H x))
           where
             test : Level.Lift ℓ' H -> Level.Lift ℓ H
             test = λ x' -> step1f {ℓ = ℓ''} {ℓ'' = ℓ'} {ℓ' = ℓ} H x'
             myfn :  Level.Lift ℓ H ->  Level.Lift ℓ' H ->  Level.Lift ℓ H
             myfn w' tyG =  test tyG
             
section-trans≡≡ :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} -> (FG : F ≡≡ G) → (GH : G ≡≡ H) -> ∀ x → transf FG GH (transg FG GH x) ≡  x
section-trans≡≡ {ℓ} {ℓ'} {ℓ''}{F}{G}{H} FG GH x = (((transfg2 FG GH x ∙ transfg4 FG GH x) ∙ transfg7 FG GH x) ∙ transfg9 GH x ) 

trans≡≡' :  ∀ {ℓ} {ℓ'} {ℓ''} {F : Set ℓ} → {G : Set ℓ'} → {H :  Set ℓ''} → F ≡≡ G → G ≡≡ H → F ≡≡ H
trans≡≡'  {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} {F = F} {G = G} {H = H} FG GH  = isoToPath (iso (transf FG GH) (transg FG GH) (section-trans≡≡ FG GH) (section-trans≡≡ (sym GH) (sym FG)))

--------------------------------------

refl≡≡ : ∀ {ℓ} {F : Set ℓ} → F ≡≡ F
refl≡≡ = refl

sym≡≡ : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → F ≡≡ G → G ≡≡ F
sym≡≡ fg' = sym fg'

sym¬≡≡  : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → ¬ (F ≡≡ G) → ¬ (G ≡≡ F)
sym¬≡≡ nfg' = λ x → nfg' (sym≡≡ x)

Sym≡≡-id-section : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → section (sym≡≡ {ℓ = ℓ} {ℓ' = ℓ'}{F = F}{G = G}) (sym≡≡ {ℓ = ℓ'} {ℓ' = ℓ})
Sym≡≡-id-section = λ b  → refl

sym≡≡-id : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (F ≡≡ G) ≡ (G ≡≡ F)
sym≡≡-id  {ℓ} {ℓ'} {F = F} {G = G} = isoToPath (iso sym≡≡ sym≡≡  Sym≡≡-id-section Sym≡≡-id-section)

sym¬≡≡-id : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (¬ (F ≡≡ G)) ≡ (¬ (G ≡≡ F))
sym¬≡≡-id  {ℓ} {ℓ'} {F = F} {G = G} = cong (λ x → ¬ x) sym≡≡-id

symSym≡≡-id  : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → {FG : F ≡≡ G} → FG ≡ (sym≡≡ (sym≡≡ FG))
symSym≡≡-id {FG = FG}  = refl

transport≡≡-id : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (FG : F ≡≡ G) → (f : F)  → transport≡≡ FG f ≡ lower (transport FG (Level.lift f))
transport≡≡-id FG f = refl

transport≡≡Refl : ∀ {ℓ} {F : Set ℓ} → (f : F) -> (transport≡≡ refl≡≡ f) ≡ f
transport≡≡Refl f = transportRefl f

transportTrans-hlp' : ∀ {ℓ}{ℓ'} {A : Set ℓ}{B : Set ℓ'}{AB : A ≡≡ B} → (x : A) → lower (transport AB (Level.lift x)) ≡ (transport≃ (≡≡→≃ AB) x)
transportTrans-hlp' x =  refl

transportTrans-hlp : ∀ {ℓ}{ℓ'} {A : Set ℓ}{B : Set ℓ'}{AB : A ≡≡ B} → (x : A) → transport≡≡ AB x ≡ (transport≃ (≡≡→≃ AB) x)
transportTrans-hlp x =  refl

-- We can define when two elements are 'equal' under '≡≡':
EqualTerm : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (F ≡≡ G) -> (f : F) -> (g : G) -> Type ℓ'
EqualTerm FG f g = (transport≡≡ FG f) ≡ g

EqualTerm-id :  ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (FG : F ≡≡ G) -> (f : F) -> (g : G) -> (EqualTerm FG f g) ≡ ((transport≡≡ FG f) ≡ g)
EqualTerm-id  FG f g = refl

EqualTerm-test :  ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → {H : Set ℓ''} → (FG : F ≡≡ G) -> (GH : G ≡≡ H) → (f : F) -> (g : G) ->
                    (transport≡≡ FG f) ≡ g → (transport≡≡ GH (transport≡≡ FG f)) ≡ (transport≡≡ GH g)
EqualTerm-test FG GH f g = cong (transport≡≡ GH)

-- It inherits some good properties as follows:
EqualTerm-sym : ∀ {ℓ} {ℓ'} {F : Set ℓ} -> {G : Set ℓ'} → (FG : F ≡≡ G) -> (f : F) -> (g : G) -> (EqualTerm FG f g) → EqualTerm (sym≡≡ FG) g f 
EqualTerm-sym FG f g eqn = sym step2 ∙ step1
                 where
                   step1 : transport≡≡ (sym FG) (transport≡≡ FG f) ≡ f
                   step1 = (transport⁻Transport≡≡ FG f)
                   step2 : transport≡≡ (sym FG) (transport≡≡ FG f) ≡ transport≡≡ (sym FG) g
                   step2 = cong (λ x →  transport≡≡ (sym FG) x) eqn

EqualTerm-refl : ∀ {ℓ} {F : Set ℓ} → (f : F) -> (f' : F) → (EqualTerm (refl≡≡ {F = F}) f f') → (f ≡ f')   
EqualTerm-refl {F = F} f f' eqn = (sym (transportRefl f)) ∙ eqn

EqualTerm-Refl' : ∀ {A : Type ℓ} {x : A} → EqualTerm refl≡≡ x x 
EqualTerm-Refl' {A = A} {x = x} = transport (sym (EqualTerm-id refl≡≡ x x)) (transport≡≡Refl x) 

toEqualTerm-refl : ∀ {ℓ} {F : Set ℓ} → (f : F) -> (f' : F) → (f ≡ f') → (EqualTerm (refl≡≡ {F = F}) f f')
toEqualTerm-refl {F = F} f f' ff' = (transportRefl f) ∙ ff'

EqualTerm-reflTrans : ∀ {ℓ} {F : Type ℓ} → {x y z : F} (p : EqualTerm refl≡≡ x y) (q : EqualTerm refl≡≡ y z) → EqualTerm refl≡≡ x z
EqualTerm-reflTrans {ℓ}{F}{x}{y}{z} p q = toEqualTerm-refl x z (EqualTerm-refl x y p ∙ EqualTerm-refl y z q)                  

subst≡≡ : ∀ {ℓ ℓ' ℓ''} {F : Type ℓ} {G : Type ℓ'}{FG : F ≡≡ G} {x : F} {y : G} → (B : F → Type ℓ'') → (p : (EqualTerm FG x y)) → B x → B (transport≡≡ (sym FG) y)  
subst≡≡ {ℓ}{ℓ'}{ℓ''}{F}{G}{FG}{x}{y} B p pa = transport (cong (λ x -> B x) (sym step3)) pa 
                                        where
                                          step1 : (EqualTerm (sym FG) y x)
                                          step1 = EqualTerm-sym FG x y p
                                          step2 : (EqualTerm (sym FG) y x) ≡ ((transport≡≡ (sym FG) y) ≡ x)
                                          step2 = refl
                                          step3 : (transport≡≡ (sym FG) y) ≡ x
                                          step3 = transport step2 step1
 
isoTo≡≡ :   {F : Type ℓ}{G : Type ℓ'} → Iso (Level.Lift ℓ' F) (Level.Lift ℓ G) → F ≡≡ G
isoTo≡≡ {F = F} {G = G} iso' = isoToPath iso'
