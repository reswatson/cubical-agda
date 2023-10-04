
{-# OPTIONS --safe #-}
{-# OPTIONS --no-main #-}
{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module ProofZisN where

open import Cubical.Foundations.Prelude hiding (Σ-syntax)
open import Cubical.Foundations.Isomorphism 
open import Cubical.Foundations.Transport

open import Data.Empty
open import Data.Nat as Nat renaming (_⊔_ to max)
open import Data.Integer as Int renaming (_⊔_ to ℤ-max)
open import Relation.Nullary
 
private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    
--------------------------------------------------

-- A rather long proof that ℤ ≡ ℕ in Cubical Agda

--------------------------------------------------

NatPlusSuc≡SucNatPlusNat : ∀ n n' → (n Nat.+ Nat.suc n') ≡ (Nat.suc (n Nat.+ n'))
NatPlusSuc≡SucNatPlusNat Nat.zero n' = refl
NatPlusSuc≡SucNatPlusNat (Nat.suc n) n' = cong (λ x -> Nat.suc x) (NatPlusSuc≡SucNatPlusNat n n')

NatPlusSuc≡SucNatPlusNat-dbl : ∀ n n' → (n Nat.+ (Nat.suc (Nat.suc n'))) ≡ (Nat.suc (Nat.suc ((n Nat.+ n'))))
NatPlusSuc≡SucNatPlusNat-dbl n n' = step1 ∙ cong (λ x → Nat.suc x) (NatPlusSuc≡SucNatPlusNat n n')
                          where
                            step1 :  (n Nat.+ (Nat.suc (Nat.suc n'))) ≡ (Nat.suc ((n Nat.+ (Nat.suc n'))))
                            step1 = NatPlusSuc≡SucNatPlusNat n (Nat.suc n') 

data isEven : ℕ → Set where
  ZisEven  : isEven 0
  SSisEven : {n : ℕ} → isEven n → isEven (Nat.suc (Nat.suc n))

data isOdd : ℕ → Set where
  1isOdd  : isOdd 1
  SSisOdd : {n : ℕ} → isOdd n → isOdd (Nat.suc (Nat.suc n))

data isNeg : ℤ → Set where
  isneg : ∀ {n} → isNeg (-[1+_] n)

data isNonNeg : ℤ → Set where
  isnonneg : ∀ {n} → isNonNeg (+ n)

isNonNeg→¬IsNeg : ∀ z → isNonNeg z → ¬ isNeg z
isNonNeg→¬IsNeg (+_ Nat.zero) isnonneg = λ ()
isNonNeg→¬IsNeg +[1+ n ] isnonneg = λ ()

¬isNeg+ : ∀ n → ¬ (isNeg (+ n ))
¬isNeg+ Nat.zero = λ () 
¬isNeg+ (Nat.suc n) = λ ()

isNeg→IsNegPred : ∀ z → isNeg z → isNeg (Int.pred z)
isNeg→IsNegPred (-[1+_] n) isN = isneg

odd→even-up : {n : ℕ} → isOdd n → isEven (Nat.suc n)
odd→even-up {n = Nat.suc .0} 1isOdd = SSisEven ZisEven
odd→even-up {n = Nat.suc .(Nat.suc _)} (SSisOdd isO) = SSisEven (odd→even-up isO)

odd→odd-up :  {n : ℕ} → isOdd n → isOdd (Nat.suc (Nat.suc n))
odd→odd-up {n = Nat.suc Nat.zero} isO = SSisOdd isO
odd→odd-up {n = Nat.suc (Nat.suc n)} isO = (SSisOdd isO)

odd→even-down : {n : ℕ} → isOdd (Nat.suc n) → isEven n
odd→even-down {n = Nat.zero} isO = ZisEven
odd→even-down {n = Nat.suc n} (SSisOdd isO) = odd→even-up isO

isEven-down :  {n : ℕ} → (isEven (Nat.suc (Nat.suc n))) → (isEven n)
isEven-down {n = Nat.zero} ne = ZisEven
isEven-down {n = Nat.suc n} (SSisEven ne) = ne

isEven-up :  {n : ℕ} → (isEven n) → (isEven (Nat.suc (Nat.suc n)))
isEven-up {n = Nat.zero} ne = SSisEven ne
isEven-up {n = Nat.suc (Nat.suc n)} (SSisEven ne) = SSisEven (isEven-up ne)

even→odd-down : {n : ℕ} →  isEven (Nat.suc n) → isOdd n
even→odd-down {n = Nat.suc Nat.zero} isE = 1isOdd
even→odd-down {n = Nat.suc (Nat.suc n)} isE = odd→odd-up step2
                         where
                           step1 : isEven (Nat.suc n)
                           step1 = isEven-down isE
                           step2 : isOdd n
                           step2 = even→odd-down step1

notEven→NotEven-up : {n : ℕ} → ¬ (isEven n) → ¬ (isEven (Nat.suc (Nat.suc n)))
notEven→NotEven-up {n = Nat.zero} ne = ⊥-elim (ne ZisEven)
notEven→NotEven-up {n = Nat.suc n} ne = λ x → ne (isEven-down x)

notEven→NotEven-down : {n : ℕ} → ¬ (isEven (Nat.suc (Nat.suc n))) → ¬ (isEven n)
notEven→NotEven-down {n = n} ne = λ x -> ne (SSisEven x)

isEven→NotIsEven-down : ∀ n → isEven (Nat.suc n) → ¬ (isEven n)
isEven→NotIsEven-down (Nat.suc Nat.zero) isE = λ ()
isEven→NotIsEven-down (Nat.suc (Nat.suc (Nat.suc n))) (SSisEven isE) = notEven→NotEven-up (isEven→NotIsEven-down (Nat.suc n) isE)

isEven-n+n : ∀ n → isEven (n Nat.+ n)
isEven-n+n Nat.zero = ZisEven
isEven-n+n (Nat.suc n) = transport⁻ step1 step2
                   where
                     step1 : isEven (Nat.suc (n Nat.+ Nat.suc n)) ≡ isEven (Nat.suc (Nat.suc (n Nat.+ n))) 
                     step1 = cong (λ x → isEven (Nat.suc x)) (NatPlusSuc≡SucNatPlusNat n n)
                     step2 :  isEven (Nat.suc (Nat.suc (n Nat.+ n)))
                     step2 = SSisEven (isEven-n+n n)

¬IsEven-sucn+n : ∀ n → ¬ isEven (Nat.suc (n Nat.+ n))
¬IsEven-sucn+n n = λ x → ⊥-elim ((isEven→NotIsEven-down (n Nat.+ n) x) (isEven-n+n n))

oddNotEven : ∀ {n} → isOdd n → ¬ (isEven n)
oddNotEven {n = Nat.zero} = λ ()
oddNotEven {n = (Nat.suc Nat.zero)} = λ _ ()
oddNotEven {n = (Nat.suc (Nat.suc n))} (SSisOdd isO) = notEven→NotEven-up (oddNotEven isO)
                      where
                        step1 : isEven (Nat.suc n)
                        step1 = odd→even-down (SSisOdd isO)
                        step2 : ¬ (isEven n)
                        step2 = oddNotEven {n = n} isO

isEven→NotIsEven-up : ∀ n → isEven n → ¬ (isEven (Nat.suc n))
isEven→NotIsEven-up Nat.zero isE = λ ()
isEven→NotIsEven-up (Nat.suc (Nat.suc n)) isE = oddNotEven (odd→odd-up (even→odd-down isE))

notEvenIsOdd : ∀ {n} → ¬ (isEven n) -> isOdd n
notEvenIsOdd {n = Nat.zero} nE = ⊥-elim (nE ZisEven)
notEvenIsOdd {n = Nat.suc Nat.zero} nE = 1isOdd
notEvenIsOdd {n = Nat.suc (Nat.suc n)} nE = odd→odd-up step2
                       where
                         step1 : ¬ (isEven n)
                         step1 = notEven→NotEven-down nE
                         step2 : isOdd n
                         step2 = notEvenIsOdd step1

IsNegPredOfNeg : ∀ z → isNeg z → isNeg (Int.pred z)
IsNegPredOfNeg (-[1+_] n) isneg = isneg

isNegSucNZ→IsNeg : ∀ z → isNeg (Int.suc z) → isNeg z
isNegSucNZ→IsNeg (-[1+_] n) isN = isneg

IsNonNegSucOfNonNeg : ∀ z → isNonNeg z → isNonNeg (Int.suc z)
IsNonNegSucOfNonNeg (+_ n) isnonneg = isnonneg

isEvenDec : ∀ n → Dec (isEven n)
isEvenDec Nat.zero = yes ZisEven
isEvenDec (Nat.suc Nat.zero) = no ( (λ x → ⊥-elim (step1 x)))
                         where
                           step1 : ¬ (isEven 1)
                           step1 = λ x → oddNotEven 1isOdd x  
isEvenDec (Nat.suc (Nat.suc n)) with (isEvenDec n)  
...                               | yes x  = yes (SSisEven x)
...                               | no y = no (notEven→NotEven-up y) 

isNegDec :  ∀ z → Dec (isNeg z)
isNegDec (+_ z) = no (λ ())
isNegDec (-[1+_] z) = yes isneg

ℤ→ℕ : ℤ → ℕ
ℤ→ℕ (+_ n) = Nat._+_ n n   -- 0 2 4 6...
ℤ→ℕ (-[1+_] n) = Nat.suc (Nat._+_ n n)  -- 1 3 5 7...

ℕ→ℤ : ℕ → ℤ
ℕ→ℤ Nat.zero = + 0
ℕ→ℤ (Nat.suc Nat.zero) = -[1+_] Nat.zero
ℕ→ℤ (Nat.suc (Nat.suc n)) with (isEvenDec n)
ℕ→ℤ (Nat.suc (Nat.suc n))   | yes x  = Int.suc (ℕ→ℤ n)  
ℕ→ℤ (Nat.suc (Nat.suc n))   | no y  =  Int.pred (ℕ→ℤ n)   

ℕ→ℤsucsuc-even-id : ∀ n → isEven n → ℕ→ℤ (Nat.suc (Nat.suc n)) ≡ Int.suc (ℕ→ℤ n) 
ℕ→ℤsucsuc-even-id n isE with (isEvenDec n) 
...                      | yes x = refl
...                      | no y = ⊥-elim (y isE)

ℕ→ℤsucsuc-odd-id : ∀ n → ¬ isEven n → ℕ→ℤ (Nat.suc (Nat.suc n)) ≡ Int.pred (ℕ→ℤ n) 
ℕ→ℤsucsuc-odd-id n isE with (isEvenDec n) 
...                      | no x = refl
...                      | yes y = ⊥-elim (isE y)

ℕ→ℤ+-id : ∀ n →  ℕ→ℤ (n Nat.+ n) ≡ + n
ℕ→ℤ+-id Nat.zero = refl
ℕ→ℤ+-id (Nat.suc n) with (isEvenDec (n Nat.+ n)) 
...                  | yes x = step1 ∙ step2 ∙ step3
                        where
                          step1 :  ℕ→ℤ (Nat.suc (n Nat.+ Nat.suc n)) ≡ ℕ→ℤ (Nat.suc (Nat.suc (n Nat.+ n)))
                          step1 =  cong (λ x →  ℕ→ℤ (Nat.suc x)) (NatPlusSuc≡SucNatPlusNat n n)
                          step2 :  ℕ→ℤ (Nat.suc (Nat.suc (n Nat.+ n))) ≡ Int.suc (ℕ→ℤ (n Nat.+ n))
                          step2 = ℕ→ℤsucsuc-even-id (n Nat.+ n) x
                          step3 : Int.suc (ℕ→ℤ (n Nat.+ n)) ≡ Int.suc (+ n)
                          step3 = cong (λ x → Int.suc x) (ℕ→ℤ+-id n)
                          step4 : Int.suc (+ n) ≡ +[1+ n ]
                          step4 = refl
...                  | no y = ⊥-elim (y (isEven-n+n n))

ℕ→ℤSuc+-id-hlp' :  ∀ n → (Int.pred -[1+ n ]) ≡ -[1+ (Nat.suc n) ]
ℕ→ℤSuc+-id-hlp' Nat.zero = refl
ℕ→ℤSuc+-id-hlp' (Nat.suc n) = refl

ℕ→ℤSuc+-id-hlp :  ∀ n → Int.pred (Int.pred -[1+ n ]) ≡ -[1+ Nat.suc (Nat.suc n) ]
ℕ→ℤSuc+-id-hlp Nat.zero = refl
ℕ→ℤSuc+-id-hlp (Nat.suc n) = refl

ℕ→ℤSuc+-id : ∀ n →  ℕ→ℤ (Nat.suc (n Nat.+ n)) ≡ -[1+ n ]
ℕ→ℤSuc+-id Nat.zero = refl
ℕ→ℤSuc+-id (Nat.suc Nat.zero) = refl
ℕ→ℤSuc+-id (Nat.suc (Nat.suc n)) = step1 ∙ step2
            where
              step1 : (ℕ→ℤ (Nat.suc (Nat.suc (Nat.suc (n Nat.+ Nat.suc (Nat.suc n))))) ≡ ℕ→ℤ (Nat.suc (Nat.suc (Nat.suc (Nat.suc (Nat.suc (n Nat.+ n)))))))
              step1 = cong (λ x → (ℕ→ℤ (Nat.suc (Nat.suc (Nat.suc x))))) (NatPlusSuc≡SucNatPlusNat-dbl n n)
              step6 : ℕ→ℤ (Nat.suc (Nat.suc (Nat.suc (Nat.suc (Nat.suc (n Nat.+ n)))))) ≡ (Int.pred (ℕ→ℤ  (Nat.suc (Nat.suc (Nat.suc (n Nat.+ n))))))
              step6 = ℕ→ℤsucsuc-odd-id (Nat.suc (Nat.suc (Nat.suc (n Nat.+ n)))) (notEven→NotEven-up (¬IsEven-sucn+n n)) 
              step7 : ℕ→ℤ (Nat.suc (Nat.suc (Nat.suc (n Nat.+ n)))) ≡ (Int.pred (ℕ→ℤ (Nat.suc (n Nat.+ n))))
              step7 = ℕ→ℤsucsuc-odd-id (Nat.suc (n Nat.+ n)) (¬IsEven-sucn+n n)  
              step3 : ℕ→ℤ (Nat.suc (Nat.suc (Nat.suc (Nat.suc (Nat.suc (n Nat.+ n)))))) ≡ (Int.pred (Int.pred (ℕ→ℤ (Nat.suc (n Nat.+ n)))))
              step3 = step6 ∙ cong (λ x → Int.pred x) step7 
              step5 : Int.pred (Int.pred (ℕ→ℤ (Nat.suc (n Nat.+ n)))) ≡ Int.pred (Int.pred -[1+ n ])
              step5 = cong (λ x → Int.pred (Int.pred x)) (ℕ→ℤSuc+-id n)
              step4 : Int.pred (Int.pred -[1+ n ]) ≡ -[1+ Nat.suc (Nat.suc n) ]
              step4 = ℕ→ℤSuc+-id-hlp n 
              step2 : ℕ→ℤ (Nat.suc (Nat.suc (Nat.suc (Nat.suc (Nat.suc (n Nat.+ n)))))) ≡ -[1+ Nat.suc (Nat.suc n) ]
              step2 = step3 ∙ step5 ∙ step4

ℤ→ℕIntPred≡ : ∀ z → isNeg z → ℤ→ℕ (Int.pred z) ≡ Nat.suc (Nat.suc (ℤ→ℕ z))
ℤ→ℕIntPred≡ (+_ n) = λ ()
ℤ→ℕIntPred≡ (-[1+_] n) isn = cong (λ x → Nat.suc (Nat.suc x)) (NatPlusSuc≡SucNatPlusNat n n)

ℤ→ℕIntSuc≡ : ∀ z → (isNonNeg z) → ℤ→ℕ (Int.suc z) ≡ Nat.suc (Nat.suc (ℤ→ℕ z))
ℤ→ℕIntSuc≡ (+_ n) nn = cong (λ x → (Nat.suc x)) (NatPlusSuc≡SucNatPlusNat n n) 

¬isEven→isNeg : ∀ n → ¬ (isEven n) → isNeg (ℕ→ℤ n)
¬isEven→isNeg Nat.zero nE = ⊥-elim (nE ZisEven)
¬isEven→isNeg (Nat.suc Nat.zero) nE = isneg
¬isEven→isNeg (Nat.suc (Nat.suc n)) nE = transport⁻ step5 step4
                              where
                                step1 : ¬ (isEven n)
                                step1 = notEven→NotEven-down nE
                                step2 : isNeg (ℕ→ℤ n)
                                step2 = ¬isEven→isNeg n step1
                                step3 : ℕ→ℤ (Nat.suc (Nat.suc n)) ≡ Int.pred (ℕ→ℤ n)
                                step3 = ℕ→ℤsucsuc-odd-id n (notEven→NotEven-down nE)
                                step4 : isNeg (Int.pred (ℕ→ℤ n))
                                step4 = IsNegPredOfNeg (ℕ→ℤ n) step2
                                step5 : isNeg (ℕ→ℤ (Nat.suc (Nat.suc n))) ≡ isNeg (Int.pred (ℕ→ℤ n))
                                step5 = cong (λ x → isNeg x) step3

isNegNZsucsuc≡ : ∀ n → isNeg (ℕ→ℤ (Nat.suc (Nat.suc n))) → isNeg (ℕ→ℤ n)
isNegNZsucsuc≡ (Nat.suc Nat.zero) isN = isneg
isNegNZsucsuc≡ (Nat.suc (Nat.suc n)) isN with (isEvenDec n) 
...                                       | yes x = isNegSucNZ→IsNeg (Int.suc (ℕ→ℤ n)) (transport step4 isN)
                                                    where
                                                      step4 : isNeg (Int.suc (ℕ→ℤ (Nat.suc (Nat.suc n)))) ≡ isNeg (Int.suc (Int.suc (ℕ→ℤ n)))
                                                      step4 = cong (λ v → (isNeg (Int.suc v))) (ℕ→ℤsucsuc-even-id n x)   
...                                       | no y = isNeg→IsNegPred (ℕ→ℤ n) (¬isEven→isNeg n y)

isNegNZ→¬Even : ∀ n → isNeg (ℕ→ℤ n) → ¬ (isEven n)
isNegNZ→¬Even (Nat.suc Nat.zero) isN = isEven→NotIsEven-down (Nat.suc Nat.zero) (SSisEven ZisEven)
isNegNZ→¬Even (Nat.suc (Nat.suc n)) isN = notEven→NotEven-up (isNegNZ→¬Even n (isNegNZsucsuc≡ n isN))

¬isEven→ℕ→ℤisNeg-hlp : ∀ n → isNeg (ℕ→ℤ n) → isNeg (ℕ→ℤ (Nat.suc (Nat.suc n)))
¬isEven→ℕ→ℤisNeg-hlp (Nat.suc Nat.zero) isn = isneg
¬isEven→ℕ→ℤisNeg-hlp (Nat.suc (Nat.suc n)) isn with (isEvenDec n) 
...                                             | yes x = ⊥-elim (step2 x)
                                                     where
                                                       step1 : isNeg (ℕ→ℤ n)
                                                       step1 = isNegSucNZ→IsNeg (ℕ→ℤ n) isn
                                                       step2 : ¬ (isEven n)
                                                       step2 = isNegNZ→¬Even n (isNegSucNZ→IsNeg (ℕ→ℤ n) isn)
...                                             | no y = transport⁻ step3 step1
                                                   where
                                                     step1 : isNeg (Int.pred (Int.pred (ℕ→ℤ n)))
                                                     step1 = IsNegPredOfNeg (Int.pred (ℕ→ℤ n)) isn
                                                     step2 : ℕ→ℤ (Nat.suc (Nat.suc n)) ≡ Int.pred (ℕ→ℤ n) 
                                                     step2 = ℕ→ℤsucsuc-odd-id n y
                                                     step3 : isNeg (Int.pred (ℕ→ℤ (Nat.suc (Nat.suc n)))) ≡ isNeg (Int.pred (Int.pred (ℕ→ℤ n)))
                                                     step3 = cong (λ x → isNeg (Int.pred x)) step2
¬isEven→isNegℕ→ℤ : ∀ n → ¬ (isEven n) → isNeg (ℕ→ℤ n)
¬isEven→isNegℕ→ℤ Nat.zero nE = ⊥-elim (nE ZisEven)
¬isEven→isNegℕ→ℤ (Nat.suc Nat.zero) nE = isneg
¬isEven→isNegℕ→ℤ (Nat.suc (Nat.suc n)) nE with (isEvenDec n) 
...                                         | yes x = ⊥-elim (nE (isEven-up x))
...                                         | no y = IsNegPredOfNeg (ℕ→ℤ n) step1
                                      where
                                        step1 : isNeg (ℕ→ℤ n)
                                        step1 = ¬isEven→isNeg n y

IntPredℕ→ℤ≡ : ∀ n → ¬ (isEven n) → Int.pred (ℕ→ℤ n) ≡ (ℕ→ℤ (Nat.suc (Nat.suc n)))
IntPredℕ→ℤ≡ Nat.zero nE =  ⊥-elim (nE ZisEven)
IntPredℕ→ℤ≡ (Nat.suc Nat.zero) nE = refl
IntPredℕ→ℤ≡ (Nat.suc (Nat.suc n)) nE with (isEvenDec n) 
...                                   | yes x = ⊥-elim (nE (SSisEven x))             
...                                   | no y = cong (λ x ->  -[1+ 0 ] Int.+ x) (IntPredℕ→ℤ≡ n y) 

¬IsNegℕ→ℤSucSuc→ : ∀ n → ¬ isNeg (ℕ→ℤ (Nat.suc (Nat.suc n))) → ¬ isNeg (ℕ→ℤ n)
¬IsNegℕ→ℤSucSuc→ Nat.zero nn = λ x → ⊥-elim (step1 x)
                                  where
                                    step1 : ¬ (isNeg (+ 0))
                                    step1 = λ ()
¬IsNegℕ→ℤSucSuc→ (Nat.suc n) nn with (isNegDec (ℕ→ℤ (Nat.suc n))) 
...                              | yes x = λ v → nn (¬isEven→ℕ→ℤisNeg-hlp ((Nat.suc n)) x)
...                              | no y = λ v → y v

¬isNeg→IsEven : ∀ n → ¬ isNeg (ℕ→ℤ n) → isEven n
¬isNeg→IsEven Nat.zero isn = ZisEven
¬isNeg→IsEven (Nat.suc Nat.zero) isn = ⊥-elim (isn isneg)
¬isNeg→IsEven (Nat.suc (Nat.suc n)) isn = SSisEven (¬isNeg→IsEven n (¬IsNegℕ→ℤSucSuc→ n isn))

isEven→ℕ→ℤisNonNeg :  ∀ n → isEven n → isNonNeg (ℕ→ℤ n)
isEven→ℕ→ℤisNonNeg Nat.zero isE = isnonneg
isEven→ℕ→ℤisNonNeg (Nat.suc (Nat.suc n)) (SSisEven isE) = transport (sym step5) step3
                                        where
                                          step1 : isEven (Nat.suc (Nat.suc n))
                                          step1 = isEven-up isE
                                          step2 : ℕ→ℤ (Nat.suc (Nat.suc n)) ≡ Int.suc (ℕ→ℤ n)
                                          step2 = ℕ→ℤsucsuc-even-id n isE
                                          step4 : isNonNeg (ℕ→ℤ n)
                                          step4 = isEven→ℕ→ℤisNonNeg n isE
                                          step3 : isNonNeg (Int.suc (ℕ→ℤ n))
                                          step3 = IsNonNegSucOfNonNeg (ℕ→ℤ n) step4
                                          step5 : isNonNeg (ℕ→ℤ (Nat.suc (Nat.suc n))) ≡ isNonNeg (Int.suc (ℕ→ℤ n))
                                          step5 = cong (λ x → isNonNeg x) step2

¬isEven→ℕ→ℤisNeg : ∀ n → ¬ isEven n → isNeg (ℕ→ℤ n)
¬isEven→ℕ→ℤisNeg Nat.zero nE = ⊥-elim (nE ZisEven)
¬isEven→ℕ→ℤisNeg (Nat.suc Nat.zero) nE = isneg
¬isEven→ℕ→ℤisNeg (Nat.suc (Nat.suc n)) nE = ¬isEven→ℕ→ℤisNeg-hlp n (¬isEven→ℕ→ℤisNeg n (notEven→NotEven-down nE))

ℕ→ℤ-ℤ→ℕ-hlp-even-hlp : ∀ n → isEven n → ℤ→ℕ (Int.suc (ℕ→ℤ n)) ≡ Nat.suc (Nat.suc (ℤ→ℕ (ℕ→ℤ n)))
ℕ→ℤ-ℤ→ℕ-hlp-even-hlp n isE = ℤ→ℕIntSuc≡ (ℕ→ℤ n) (isEven→ℕ→ℤisNonNeg n isE) 

ℕ→ℤ-ℤ→ℕ-hlp-even :  ∀ {n} → ℤ→ℕ (ℕ→ℤ n) ≡ n → isEven n → ℤ→ℕ (Int.suc (ℕ→ℤ n)) ≡ Nat.suc (Nat.suc n)
ℕ→ℤ-ℤ→ℕ-hlp-even {n = n} ZN isE =  (ℕ→ℤ-ℤ→ℕ-hlp-even-hlp n isE)  ∙ cong (λ x → Nat.suc (Nat.suc x)) ZN 

ℕ→ℤ-ℤ→ℕ-hlp-odd-hlp : ∀ n → ¬ isEven n → ℤ→ℕ (Int.pred (ℕ→ℤ n)) ≡ Nat.suc (Nat.suc (ℤ→ℕ (ℕ→ℤ n)))
ℕ→ℤ-ℤ→ℕ-hlp-odd-hlp n isNE = ℤ→ℕIntPred≡ (ℕ→ℤ n) (¬isEven→ℕ→ℤisNeg n isNE)

ℕ→ℤ-ℤ→ℕ-hlp-odd :  ∀ {n} → ℤ→ℕ (ℕ→ℤ n) ≡ n → ¬ (isEven n) → ℤ→ℕ (Int.pred (ℕ→ℤ n)) ≡ Nat.suc (Nat.suc n)
ℕ→ℤ-ℤ→ℕ-hlp-odd {n = n} ZN isNE = (ℕ→ℤ-ℤ→ℕ-hlp-odd-hlp n isNE) ∙ cong (λ x -> Nat.suc (Nat.suc x)) ZN

ℕ→ℤ-ℤ→ℕ-hlp : ∀ {n} → ℤ→ℕ (ℕ→ℤ n) ≡ n → ℤ→ℕ (ℕ→ℤ (Nat.suc (Nat.suc n))) ≡ (Nat.suc (Nat.suc n))
ℕ→ℤ-ℤ→ℕ-hlp {n = n} ZN with (isEvenDec n) 
...                     | yes x = ℕ→ℤ-ℤ→ℕ-hlp-even ZN x
...                     | no y = ℕ→ℤ-ℤ→ℕ-hlp-odd ZN y

ℕ→ℤ-ℤ→ℕ-caseEven : ∀ {n} → isEven n → ℤ→ℕ (ℕ→ℤ n) ≡ n
ℕ→ℤ-ℤ→ℕ-caseEven {n = Nat.zero} isE = refl
ℕ→ℤ-ℤ→ℕ-caseEven {n = Nat.suc (Nat.suc n)} isE = ℕ→ℤ-ℤ→ℕ-hlp ind
                                    where
                                      ind : ℤ→ℕ (ℕ→ℤ n) ≡ n
                                      ind = ℕ→ℤ-ℤ→ℕ-caseEven (isEven-down isE)

ℕ→ℤ-ℤ→ℕ-caseOdd : ∀ {n} → ¬ isEven n → ℤ→ℕ (ℕ→ℤ n) ≡ n
ℕ→ℤ-ℤ→ℕ-caseOdd {n = Nat.zero} isNE = refl
ℕ→ℤ-ℤ→ℕ-caseOdd {n = Nat.suc Nat.zero} isNE = refl
ℕ→ℤ-ℤ→ℕ-caseOdd {n = Nat.suc (Nat.suc n)} isNE = ℕ→ℤ-ℤ→ℕ-hlp ind
                               where
                                 ind :  ℤ→ℕ (ℕ→ℤ n) ≡ n
                                 ind = ℕ→ℤ-ℤ→ℕ-caseOdd (notEven→NotEven-down isNE)

ℤ→ℕ-ℕ→ℤ-caseNeg : ∀ {z : ℤ} → isNeg z → ℕ→ℤ (ℤ→ℕ z) ≡ z
ℤ→ℕ-ℕ→ℤ-caseNeg {z = -[1+_] n} isn = ℕ→ℤSuc+-id n

ℤ→ℕ-ℕ→ℤ-caseNotNeg : ∀ {z : ℤ} → ¬ isNeg z → ℕ→ℤ (ℤ→ℕ z) ≡ z
ℤ→ℕ-ℕ→ℤ-caseNotNeg {z = +_ n} nn = ℕ→ℤ+-id n 
ℤ→ℕ-ℕ→ℤ-caseNotNeg {z = -[1+_] n} nn = ⊥-elim (nn isneg)

ℕ→ℤ-ℤ→ℕ : (n : ℕ) → ℤ→ℕ ((ℕ→ℤ) n) ≡ n
ℕ→ℤ-ℤ→ℕ n with (isEvenDec n)  
...                   | yes x = ℕ→ℤ-ℤ→ℕ-caseEven x
...                   | no y = ℕ→ℤ-ℤ→ℕ-caseOdd y

ℤ→ℕ-ℕ→ℤ : (z : ℤ) → ℕ→ℤ ((ℤ→ℕ) z) ≡ z
ℤ→ℕ-ℕ→ℤ n with (isNegDec n)  
...                   | yes x = ℤ→ℕ-ℕ→ℤ-caseNeg x 
...                   | no y = ℤ→ℕ-ℕ→ℤ-caseNotNeg y 


------------------------
------------------------

-- Note that this file creates warnings when
-- {-# OPTIONS -WnoUnsupportedIndexedMatch #-} is omitted.

ℤ≡ℕ : ℤ ≡ ℕ
ℤ≡ℕ = isoToPath (iso ℤ→ℕ ℕ→ℤ ℕ→ℤ-ℤ→ℕ ℤ→ℕ-ℕ→ℤ)

------------------------
------------------------
