module IndRes where

open import Data.Nat
open import Relation.Binary.Core
open import Data.Vec as V
open import Data.List
open import Data.List.All
open import Data.Product

open import Prelim
open import Prelim.Syntax
open import Prelim.Models
open import Prelim.Res

open AxEnvAny

-- Type class resolution

data _⊢_∷_ {n m l : ℕ} {Σ : Signature n m} {var : Set}
  {PTΣ : PTSignature l} {pVar : Set}
  (Φ : AxEnv Σ var PTΣ pVar)
  (pt : PTerm PTΣ pVar)
  (A' : At Σ var) -- A' ≡ σA
  : Set₁ where

  Lp-m : {n' : ℕ}  
    {Bᵢs : Vec (At Σ var) n'}
    {e : PTerm PTΣ pVar } →

    (σ : Subst Σ var) → 
    (A : At Σ var) →
    (wEq : (appA σ A) ≡ A') →
    (eᵢs : Vec (PTerm PTΣ pVar) n') →
    (wPt : pt ≡ ptApp e (toList eᵢs) ) →
    -- proper shape of Ei's
    All (λ { (eᵢ , Bᵢ) → Φ ⊢ eᵢ ∷ appA σ Bᵢ } )
      (toList (V.zip eᵢs Bᵢs)) →
    AEAny (λ { e ch wNECh → ch ≡ (toList Bᵢs) CH.⇒ A } ) Φ →
    Φ ⊢ pt ∷ A'

module Ex₄ where
  open import Intro
  open Ex₁

  κ₁κ₂κ₂ : PTerm PTΣ_Pair ℕ
  κ₁κ₂κ₂ = (κ₁ ~ κ₂) ~ κ₂

  ex₄ : Φ_Pair ⊢ κ₁κ₂κ₂ ∷ eq (pair (int ,' int))
  
  ex₄ = Lp-m σ (eq (pair (X ,' Y))) refl (κ₂ ∷ κ₂ ∷ []) refl
    ( Lp-m σ (eq int) refl [] refl [] ((here refl))
    ∷ Lp-m σ (eq int) refl [] refl [] (here refl)
    ∷ [])
    (there ((here refl)))
    where
      σ : Subst Σ_Pair ℕ
      σ = record { subst = λ x → int }
    

open FixPoint
open LFP

--open import Size
{-
 - Helper - map over vec
 - @TODO - monotonous in (toList (V.zip _ B) → (toList B)
 - @TODO - termination check with thm-ind-sound
 -}
map-vec : ∀ {k} 
     {B : Set}
     {E : Set}
     {Q : E × B → Set₁ }
     {R : B → Set₁ } →

     {eᵢs : Vec E k} →
     {Bᵢs : Vec B k} →
     (P : {e : E} {b : B} → Q ( e , b ) → R b) → 
     All Q 
       (toList (V.zip eᵢs Bᵢs)) →
     All R
       (toList  Bᵢs)
map-vec {eᵢs = []} {Bᵢs = []} P [] = []
map-vec {eᵢs = _ ∷ _} {_ ∷ _} P (px ∷ xs)
  = (P px) ∷ map-vec P xs


thm-ind-sound :
  ∀ {l m n} {Σ : Signature n m} → {var : Set}
  {PTΣ : PTSignature l} → {pVar : Set} 
  {Φ : AxEnv Σ var PTΣ pVar } →
  {A' : At Σ var} →
  {e : PTerm PTΣ pVar} →

  Φ ⊢ e ∷ A' → Φ ⊨ A'

thm-ind-sound (Lp-m {Bᵢs = []} _ A refl [] _ [] wCH)
 = lemma-1-a-i 
    (ae2a wCH (λ { { ch = [] CH.⇒ .A } refl → refl } ))
thm-ind-sound {i} {j} (Lp-m {_} {Bᵢs} σ A refl (eᵢs) wPt wBᵢs wCH) =
  lemma-1-b-i 
    (map-vec' wBᵢs)
    (ae2a wCH (λ { {_} {.(toList Bᵢs) CH.⇒ .A} {wCh} refl → refl } ))
  where
    {-
     - Inlined for now to satisfy termination checker
     -}
    map-vec' : ∀ {k l m n} { var : Set} {pVar : Set} →
      {Σ : Signature m n}
      {σ : Subst Σ var}
      {PTΣ : PTSignature l}
      {Φ : AxEnv Σ var PTΣ pVar} →
      {eᵢs : Vec (PTerm PTΣ pVar) k} →
      {Bᵢs : Vec (At Σ var) k} →
      All (λ { (eᵢ , Bᵢ) → Φ ⊢ eᵢ ∷ appA σ Bᵢ } )
        (toList (V.zip eᵢs Bᵢs)) →
      All (λ { Bᵢ → Φ ⊨ appA σ Bᵢ})
        (toList  Bᵢs)
    map-vec' {eᵢs = []} {Bᵢs = []} [] = []
    map-vec' {eᵢs = _ ∷ _} {Bᵢs = _ ∷ _} (px ∷ x)
      = thm-ind-sound px ∷ (map-vec' x)


