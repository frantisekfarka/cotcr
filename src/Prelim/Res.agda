module Prelim.Res where

open import Data.Nat
open import Data.List.Any as LAn

open import Prelim.Syntax

data AxEnv {n m l : ℕ}
  (Σ : Signature n m) (var : Set)
  (PTΣ : PTSignature l) (pVar : Set) : Set where

  · : AxEnv Σ var PTΣ pVar
  _,_∷_⟦_⟧  : AxEnv Σ var PTΣ pVar →
    PTerm PTΣ pVar →
    (ch : CH Σ var) →
    NoExistCH ch  →
    AxEnv Σ var PTΣ pVar

open import Data.List
open import Data.Product as P

toPrg : {n m l : ℕ }
  {Σ : Signature n m} {var : Set}
  {PTΣ : PTSignature l} {pVar : Set} →
  AxEnv Σ var PTΣ pVar → Program Σ var
toPrg x = record { prg = f x }
  where
    f : ∀ {Σ var PTΣ pVar} → AxEnv Σ var PTΣ pVar
      → List (P.Σ (CH Σ var) (λ x₁ → NoExistCH x₁))
    f · = []
    f (y , x₁ ∷ ch ⟦ wCh ⟧) = (ch , wCh) ∷ f y

module AxEnvAny where
  -- Any P xs means that at least one element in xs satisfies P.

  data AEAny {n m l : ℕ}
       {Σ : Signature n m} {var : Set}
       {PTΣ : PTSignature l} {pVar : Set}
       (P : PTerm PTΣ pVar → (ch : CH Σ var) → (NoExistCH ch)
         → Set) : AxEnv Σ var PTΣ pVar → Set where
       here  : ∀ {axe pt ch ne} (px  : P pt ch ne)
         → AEAny P (axe , pt ∷ ch ⟦ ne ⟧)
       there : ∀ {axe pt ch ne} (pxs : AEAny P axe)
         → AEAny P (axe , pt ∷ ch ⟦ ne ⟧)

  open Program
  
  ae2a : {n m l : ℕ}
       {Σ : Signature n m} {var : Set}
       {PTΣ : PTSignature l} {pVar : Set}
       {P : PTerm PTΣ pVar → (ch : CH Σ var) → (NoExistCH ch) → Set} →
       {Q : (P.Σ (CH Σ var) NoExistCH) → Set} →
       {ae : AxEnv Σ var PTΣ pVar} →
       AEAny P ae →
       (∀ {pt : PTerm PTΣ pVar} {ch : CH Σ var} {wCh : NoExistCH ch}
       → P pt ch wCh → Q (ch , wCh)) →
       Any Q (prg (toPrg ae))
  ae2a (here px) pq = here (pq px)
  ae2a (there x) pq = there (ae2a x pq)

open AxEnvAny

