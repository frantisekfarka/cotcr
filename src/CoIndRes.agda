module CoIndRes where

open import Data.Nat
open import Data.Fin
open import Relation.Binary.Core hiding ( _⇒_ )
open import Data.Vec as V
open import Data.List as L
open import Data.List.All as LAl
open import Data.List.Any as LAn
open import Data.Product

open import Prelim
open import Prelim.Syntax
open import Prelim.Models hiding ( B )
open import Prelim.Res

open AxEnvAny



module CoTCR where
-- Type class resolution with implicative reasoning

  open import Data.Product as P
{-  
  HNF : {l : ℕ} 
    {PTΣ : PTSignature l} {pVar : Set} →
    (e : PTerm PTΣ pVar) → Set
  HNF {l} {PTΣ} {pVar} e = P.Σ (Fin l × (List pVar) × List (PTerm PTΣ pVar))
    (λ { (κ , βᵢs , eᵢs) → e ≡ (λ' βᵢs ∘ ptApp (AxNode κ) eᵢs) })
-}
  data _⊢_∷_ {n m l : ℕ} {Σ : Signature n m} {var : Set}
    {PTΣ : PTSignature l} {pVar : Set}
    (Φ : AxEnv Σ var PTΣ pVar)
    (pt : PTerm PTΣ pVar)
    (H : CH Σ var) -- A' ≡ σA
    : Set₁ where

    Lp-m : {n' : ℕ}  
      {Bᵢs : Vec (At Σ var) n'}
      {e : PTerm PTΣ pVar } →
      
      (wCh : chB H ≡ [] ) →
      (σ : Subst Σ var) → 
      (A : At Σ var) →
      (wEq : (appA σ A) ≡ chH H) →
      (eᵢs : Vec (PTerm PTΣ pVar) n') →
      (wPt : pt ≡ ptApp e (toList eᵢs) ) →
      -- proper shape of Ei's
      All (λ { (eᵢ , Bᵢ) → Φ ⊢ eᵢ ∷ ([] CH.⇒ appA σ Bᵢ) } )
        (toList (V.zip eᵢs Bᵢs)) →
      AEAny (λ { e ch wNECh → ch ≡ (toList Bᵢs) CH.⇒ A } ) Φ →
      Φ ⊢ pt ∷ H

    Nu' : -- {n' : ℕ} 
      (A : At Σ var)
      (α : pVar )
      -- {βᵢs : Vec pVar n' } --^ possibly empty
      (eᵢs : List (PTerm PTΣ pVar))
      (κ : Fin l ) → -- ^ axiom of PTΣ
      (wCh : H ≡ [] ⇒ A)
      -- (wPt : pt ≡ ν α ∘ (λ' toList βᵢs ∘ ptApp (AxNode κ) eᵢs)) →
      (wPt : pt ≡ ν α ∘ (ptApp (AxNode κ) eᵢs)) →
      -- extended environment with (α :  ⇒ A)
      (Φ , PVNode α ∷ [] ⇒ A ⟦ record { noExist = λ { () } } ⟧)
        ⊢ ptApp (AxNode κ) eᵢs ∷ ([] ⇒ A) →
      Φ ⊢ pt ∷ H

  open import Data.Product as P
  open import Prelim.Syntax

  module Ex₇ where

    open import Intro
    open Ex₂


    open import Relation.Binary.PropositionalEquality
    open import Data.List.All as LAl

    α : PTerm PTΣ_EvenOdd ℕ
    α = PVNode 0

    α-v : ℕ
    α-v = 0

    κ₂-s : Fin 3
    κ₂-s = suc zero
        
    ex₇  : (Φ_EvenOdd)
      ⊢ ν α-v ∘ ((κ₂ ~ κ₃) ~ ((κ₁ ~ κ₃) ~ α)) ∷ ([] ⇒ (eq (evenList int)) )
    ex₇ = Nu' (eq (evenList int)) α-v (κ₃ ∷ ((κ₁ ~ κ₃) ~ α) ∷ []) κ₂-s refl refl
      (Lp-m refl σ (eq (evenList X)) refl (κ₃ ∷ ((κ₁ ~ κ₃) ~ α) ∷ []) refl
      ( Lp-m refl σ (eq int) refl [] refl [] (there (here refl))
      ∷ Lp-m refl σ (eq (oddList X)) refl (κ₃ ∷ α ∷ []) refl
        (Lp-m refl σ (eq int) refl [] refl [] (there (here refl))
        ∷ Lp-m refl σ (eq (evenList int)) refl [] refl [] (here refl)
        ∷ [])
        (there (there (there (here refl))))
      ∷ [])
      ( there (there (here refl)) ))
      where
        σ : Subst Σ_EvenOdd ℕ 
        σ = record { subst = λ x → int }
      



  open FixPoint
  open LFP
  open Program
  open import Data.Empty
  open import Prelim.Res
    
  open import Prelim.Res

  --
  -- Mutual-recursive for now to satisfy termination checker
  --
  map-vec' : ∀ {k l m n} { var : Set} {pVar : Set} →
      {Σ : Signature m n}
      {σ : Subst Σ var}
      {PTΣ : PTSignature l}
      {Φ : AxEnv Σ var PTΣ pVar} →
      {eᵢs : Vec (PTerm PTΣ pVar) k} →
      {Bᵢs : Vec (At Σ var) k} →

      -- thm-ind-sound made explicit
      -- ({A' : At Σ var} {e : PTerm PTΣ pVar} →
      -- Φ ⊢ e ∷ ([] ⇒ A') → toPrg Φ ⊨'' ([] ⇒ A')) →

      All (λ { (eᵢ , Bᵢ) → Φ ⊢ eᵢ ∷ ([] ⇒ appA σ Bᵢ) } )
        (toList (V.zip eᵢs Bᵢs)) →

      All (λ { Bᵢ → Φ ⊨ (appA σ Bᵢ)})
        (toList  Bᵢs)


  thm-coind-sound :
    ∀ {l m n} {Σ : Signature n m} → {var : Set}
    {PTΣ : PTSignature l} → {pVar : Set} 
    {Φ : AxEnv Σ var PTΣ pVar } →
    {A' : At Σ var} →
    {e : PTerm PTΣ pVar} →

    Φ ⊢ e ∷ ([] ⇒ A') → (toPrg Φ) ⊨'' ([] ⇒ A')
  thm-coind-sound (Lp-m refl σ A refl [] refl [] x₁) = {!!}
  thm-coind-sound (Lp-m refl σ A refl eᵢs refl x₁ x₂) = {!!}
  thm-coind-sound (Nu' A' α eᵢs κ refl refl x) = {!!}

{-
  thm-ind-sound (Lp-m {Bᵢs = []} refl σ A refl [] _ [] wCH)
    = lemma-atohc (lemma-1-a-i (ae2a wCH (λ
      { {ch = [] ⇒ .A} refl → refl })))
  thm-ind-sound (Lp-m {Bᵢs = Bᵢs} refl σ A refl eᵢs refl wBᵢs wCH)
    = lemma-atohc (lemma-1-b-i
                  (map-vec' wBᵢs)
                  (ae2a wCH ((λ {
                  {_} {.(toList Bᵢs) ⇒ .A} {_} refl → refl
                  }))))
    where
  thm-ind-sound {e = AxNode f} (Lam wCh () x)
  thm-ind-sound {e = AppNode e e₁} (Lam wCh () x)
  thm-ind-sound {e = PVNode v} (Lam wCh () x)
  thm-ind-sound {e = MuNode x e} (Lam wCh () x₁)
  thm-ind-sound {e = LamNode [] e}
    (Lam {Bᵢs = []} {[]} refl refl x₁)
      = thm-ind-sound x₁
  thm-ind-sound {e = LamNode (x ∷ x₁) e}
    (Lam {Bᵢs = []} {[]} refl () _)
  thm-ind-sound {e = LamNode x e}
    (Lam {_} {_ ∷ βᵢs'} () _ _)
-}

  map-vec' {eᵢs = []} {Bᵢs = []} {- _ -} [] = []
  map-vec' {eᵢs = _ ∷ _} {Bᵢs = _ ∷ _} {- f -} (px ∷ x)
      = lemma-chtoa (thm-coind-sound px) ∷ (map-vec' x) 


{-
  module Ex₆ where

    open Subst
    open import Size
    open import Relation.Binary.PropositionalEquality as PE hiding (subst)
    open import Level

    open import Prelim.Syntax


    ex₆ : ∀ {l m n} →
        {Σ : Signature n m} {var : Set}
        {PTΣ' : PTSignature l } {pVar : Set}
        {α : pVar} {A : At Σ var} →
        · ⊢ λ' (α ∷ []) ∘ (PVNode {PTΣ = PTΣ'} α) ∷ ((A ∷ []) ⇒ A)
    ex₆ {_} {α = α} {A = A} =
      Lam refl refl
        (Lp-m refl σ-id A (lemma-σ-id-atom A) [] refl [] (here refl))

-}
