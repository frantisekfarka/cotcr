module Prelim.Models where


open import Data.List as Lst
open import Data.List.Any as LAn
open import Data.List.All as LAl
open import Data.Nat
open import Data.Product as P

open import Level as L

open import Relation.Binary.Core
open import Relation.Unary hiding ( U )

open import Prelim.Syntax
open import Prelim.Res

-- Herbrand Universe

U : {n m : ℕ} → (Σ : Signature n m) → Set
U Σ = GTerm Σ

-- Herbrand Base

B : {n m : ℕ} → (Σ : Signature n m) → Set
B Σ = GAt Σ


open GSubst
open Subst
open NoExistCH
open AtIsGInstOf
open CHIsGInstOf

-- ground instance of NE-CH resulting from At

foo : {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  (gh : GAt Σ) →
  (ch : CH Σ var) →
  NoExistCH ch →
  AtIsGInstOf gh (chH ch) →
  
  P.Σ (GCH Σ) (λ gch → CHIsGInstOf gch ch)
foo gh ([] CH.⇒ h) neCh wGh
  = ([] CH.⇒ gh)
  , (record
    { s' = gsubst (s wGh)
    ; eqH = wGh
    ; eqB = []
    })
foo gh ((chb₁ ∷ chb) CH.⇒ h) neCh wGh
  with foo gh (chb CH.⇒ h) (record
    { noExist = λ { {v} y → noExist neCh (there y) } })
    wGh 
...| (gchb CH.⇒ _ , wGch )
  = ((gAppA (s wGh ) chb₁ ∷ gchb ) CH.⇒ gh)
  , record
    { s' = gsubst (s wGh)
    ; eqH = wGh
    ; eqB = (record
      { s = s wGh
      ; eq = refl
      }) ∷ eqB wGch }


-- Semantic operator
-- 
postulate T : {n m : ℕ} → {Σ : Signature n m} → {var : Set} → Program Σ var → Pred (B Σ) L.zero → Pred (B Σ) L.zero


record FixPoint {A : Set} (F : Pred A L.zero → Pred A L.zero) : Set₁ where
  field
    fp : Pred A L.zero
    wFp : fp ≡ F fp
open FixPoint


record LFP {A : Set} (F : Pred A L.zero → Pred A L.zero) : Set₁ where
  field
    lfp : FixPoint F
    wLfp : (fp' : FixPoint F) → fp lfp ⊆ fp fp'
open LFP

postulate M : {n m : ℕ} → {Σ : Signature n m} → {var : Set} → (P : Program Σ var) → LFP (T P) 


record GFP {A : Set} (F : Pred A L.zero → Pred A L.zero) : Set₁ where
  field
    gfp : FixPoint F
    wGfp : (fp' : FixPoint F) → fp fp' ⊆ fp gfp

postulate M' : {n m : ℕ} → {Σ : Signature n m} → {var : Set} → (P : Program Σ var) → GFP (T P)


--
-- Validity of an atom
--
record AtValid {n m : ℕ} {Σ : Signature n m} {var : Set}
  (I : Pred (B Σ) L.zero) (at : At Σ var) : Set₁ where
  field
    wVal : ∀ {σ : GSubst Σ var} →
      (gAppA σ at ∈ I)

-- Shorthand for AxEnv
-- @TODO  move to Res?
_⊨_ : ∀ {l m n} {Σ : Signature n m} → {var : Set}
  {PTΣ : PTSignature l} → {pVar : Set} 

  (Φ : AxEnv Σ var PTΣ pVar ) →
  (A : At Σ var) →
  Set₁
Φ ⊨ A = AtValid (fp (lfp (M (toPrg Φ)))) A

--
-- Validity of a formula
--
record CHValid {n m : ℕ} {Σ : Signature n m} {var : Set}
  (I : Pred (GAt Σ) L.zero) (ch : CH Σ var) : Set₁ where
  field
    wVal : ∀ {σ : Subst Σ var} →
      All (λ t → AtValid I (appA σ t)) (chB ch)
      → AtValid I (appA σ (chH ch))

open AtValid
open CHValid


-- Shorthand for AxEnv
-- @TODO  move to Res?
_⊨'_ : ∀ {l m n} {Σ : Signature n m} → {var : Set}
  {PTΣ : PTSignature l} → {pVar : Set} 

  (Φ : AxEnv Σ var PTΣ pVar ) →
  (A : CH Σ var) →
  Set₁
Φ ⊨' A = CHValid (fp (lfp (M (toPrg Φ)))) A

-- Shorthand for Program
-- @TODO  move to Res?
_⊨''_ : ∀ {m n} {Σ : Signature n m} → {var : Set} →

  (Φ : Program Σ var) →
  (H : CH Σ var) →
  Set₁
Φ ⊨'' H = CHValid (fp (lfp (M Φ))) H




open Program

--
-- Lemma 1, inductive part
--
-- a/
postulate lemma-1-a-i : {n m : ℕ} {-
-} {Σ : Signature n m} {var : Set} {-
-} {P : Program Σ var} {B : At Σ var} {-
-} {σ : Subst Σ var} → {- 
-} Any  ( λ { (ch , wNECh) → ch ≡ ([] CH.⇒ B) }) (prg P) → AtValid (fp (lfp (M P))) (appA σ B)

postulate lemma-1-b-i : {n m : ℕ} {-
-} {Σ : Signature n m} {var : Set} {-
-} {P : Program Σ var} {A : At Σ var} {Bs : List (At Σ var)} {-
-} {σ : Subst Σ var} → {-
-} All (λ Bᵢ → AtValid (fp (lfp (M P))) (appA σ Bᵢ)) Bs → {-
-} Any  ( λ { (ch , wNECh) → ch ≡ (Bs CH.⇒ A) }) (prg P) → AtValid (fp (lfp (M P))) (appA σ A)


--
-- Lemma: P ⊨ A → ∀ σ, P ⊨ σA
--
postulate lemma-inst : {n m : ℕ} {-
-} {Σ : Signature n m} {var : Set} {-
-} {P : Program Σ var} {A : At Σ var} → {-
-} AtValid (fp (lfp (M P))) A → {-
-} (σ : Subst Σ var) → {- 
-} AtValid (fp (lfp (M P))) (appA σ A)


postulate lemma-atohc : {m n : ℕ} {-
-} {Σ : Signature m n} {var : Set} {-
-} {P : Program Σ var} {A : At Σ var} → {-
-} AtValid (fp (lfp (M P))) A → {-
-} CHValid (fp (lfp (M P))) ([] CH.⇒ A) 

postulate lemma-chtoa : {m n : ℕ} {-
-} {Σ : Signature m n} {var : Set} {-
-} {P : Program Σ var} {A : At Σ var} → {-
-} CHValid (fp (lfp (M P))) ([] CH.⇒ A) → {-
-} AtValid (fp (lfp (M P))) (A) 


postulate lemma-2 : {n m : ℕ} {-
-} {Σ : Signature n m} {var : Set} {-
-} {P : Program Σ var} {A : At Σ var} {-
-} {Bs : List (At Σ var)} → {-
-} (extPrg P (Lst.map (λ B → (([] CH.⇒ B) , record { noExist = λ { () } } ) ) Bs)) ⊨'' ([] CH.⇒ A) {-
-} → P ⊨'' ([] CH.⇒ A)
