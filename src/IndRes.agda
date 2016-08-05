module IndRes where

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


module TCRes where
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
  thm-ind-sound (Lp-m {_} {Bᵢs} σ A refl (eᵢs) wPt wBᵢs wCH)
    = lemma-1-b-i 
        (map-vec' wBᵢs)
        (ae2a wCH (λ {
          {_} {.(toList Bᵢs) CH.⇒ .A} {wCh} refl → refl
        } ))
    where
      --
      -- Inlined for now to satisfy termination checker
      --
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


module TCResLam where
-- Type class resolution with implicative reasoning

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

    Lam : {n' : ℕ }
      {Bᵢs : Vec (At Σ var) n'}
      {βᵢs : Vec pVar n' }
      {e : PTerm PTΣ pVar} →
      (wCh : chB H ≡ toList Bᵢs) →
      (wPt : pt ≡ λ' (toList βᵢs) ∘ e) →

      -- extended environment with (βᵢ : ⇒ Bᵢ)'s
      extEnv Φ (L.zipWith (λ {
             βᵢ Bᵢ → PVNode βᵢ , ([] ⇒ Bᵢ) , record {
               noExist = λ { () }
             }
        }) (toList βᵢs) (toList Bᵢs)) ⊢ e ∷ ([] ⇒ chH H) →
      Φ ⊢ pt ∷ H


  module Ex₅ where

    Σ_Φ : Signature 0 3
    Σ_Φ = record { arF = λ { () } ; arP = λ x → 0 }

    A B C : At Σ_Φ ℕ
    A = PNode zero []
    B = PNode (suc zero) []
    C = PNode (suc (suc zero)) []

    A⇒B : CH Σ_Φ ℕ
    A⇒B = (A ∷ []) ⇒ B

    B⇒C : CH Σ_Φ ℕ
    B⇒C = (B ∷ []) ⇒ C

    A⇒C :
      CH Σ_Φ ℕ
    A⇒C = (A ∷ []) ⇒ C

    PTΣ_Φ : PTSignature 2
    PTΣ_Φ = record {}
    
    κ₁ : ∀ {pVar : Set} →
      PTerm PTΣ_Φ pVar
    κ₁ = AxNode zero

    κ₂ : ∀ {pVar : Set} →
      PTerm PTΣ_Φ pVar
    κ₂ = AxNode (suc zero)

    Φ : ∀ {pVar : Set} →
      AxEnv Σ_Φ ℕ PTΣ_Φ pVar
    Φ = (·
      , κ₁ ∷ A⇒B ⟦ record { noExist = λ
        { (here ())
        ; (there ())
        } } ⟧)
      , κ₂ ∷ B⇒C ⟦ record { noExist = λ
        { (here ())
        ; (there ())
        } } ⟧

    ex₅ : ∀ {pVar : Set} {α : pVar} →
      Φ ⊢ λ' (α ∷ []) ∘ (κ₂ ~ (κ₁ ~ (PVNode α))) ∷ (A⇒C)
    ex₅ {_} {α} = Lam
      refl
      refl
      (
      Lp-m refl σ-id C refl (κ₁ ~ (PVNode α) ∷ []) refl
        (Lp-m refl σ-id B refl (PVNode α ∷ []) refl
          ( Lp-m refl σ-id A refl [] refl [] (here refl)
          ∷ [])
          (there (there (here refl)))
          ∷ []
        )
        (there (here refl))
      )


  open FixPoint
  open LFP
  open Program
  open import Data.Empty
  open import Prelim.Res
    
  postulate lemma-2 : {n m : ℕ} {-
    -} {Σ : Signature n m} {var : Set} {-
    -} {P : Program Σ var} {A : At Σ var} {-
    -} {Bs : List (At Σ var)} → {-
    -} (extPrg P (L.map (λ
               B → ([] ⇒ B , record { noExist = λ { () } } )
               ) Bs)) ⊨'' ([] ⇒ A) {-
    -} → P ⊨'' ([] ⇒ A)

  open import Prelim.Res

  thm-ind-sound :
    ∀ {l m n} {Σ : Signature n m} → {var : Set}
    {PTΣ : PTSignature l} → {pVar : Set} 
    {Φ : AxEnv Σ var PTΣ pVar } →
    {A' : At Σ var} →
    {e : PTerm PTΣ pVar} →

    Φ ⊢ e ∷ ([] ⇒ A') → (toPrg Φ) ⊨'' ([] ⇒ A')
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
      --
      -- Inlined for now to satisfy termination checker
      --
      map-vec' : ∀ {k l m n} { var : Set} {pVar : Set} →
        {Σ : Signature m n}
        {σ : Subst Σ var}
        {PTΣ : PTSignature l}
        {Φ : AxEnv Σ var PTΣ pVar} →
        {eᵢs : Vec (PTerm PTΣ pVar) k} →
        {Bᵢs : Vec (At Σ var) k} →
        All (λ { (eᵢ , Bᵢ) → Φ ⊢ eᵢ ∷ ([] ⇒ appA σ Bᵢ) } )
          (toList (V.zip eᵢs Bᵢs)) →
        All (λ { Bᵢ → Φ ⊨ (appA σ Bᵢ)})
          (toList  Bᵢs)
      map-vec' {eᵢs = []} {Bᵢs = []} [] = []
      map-vec' {eᵢs = _ ∷ _} {Bᵢs = _ ∷ _} (px ∷ x)
        = lemma-chtoa (thm-ind-sound px) ∷ (map-vec' x) 
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

  module Ex₆ where
  
{-    ex₆ : ∀ {l m n} →
        {Σ : Signature n m} {var : Set}
        {PTΣ' : PTSignature l } {pVar : Set}
        {α : pVar} {A : At Σ var} →
      · ⊢ λ' (α ∷ []) ∘ (PVNode {PTΣ = PTΣ'} α) ∷ ((A ∷ []) ⇒ A)
    ex₆ {_} {α} = Lam {!!} {!!} {!!}
-}
{-
    ex₆' : ∀ {l m n} →
        {Σ : Signature n m} {var : Set}
        {PTΣ' : PTSignature l } {pVar : Set}
        {α : pVar} {A : At Σ var} →
      ( · , PVNode α ∷ ([]) ⇒ A ⟦ record { noExist = λ { () } } ⟧) ⊢ PVNode {PTΣ = PTΣ'} α ∷ ([] ⇒ A)
    ex₆' {α = α} {A = A} with appA σ-id A
    ex₆' {α = α} {A = A} | z = {!!} -- Lp-m refl σ-id A refl [] refl [] (here refl)
-}

    open Subst
    open import Size


    open import Relation.Binary.PropositionalEquality as PE hiding (subst)
    open import Level


    zap : ∀ {i : Size} {j : Size< i} {n m : ℕ} {var : Set} {Σ : Signature n m}
        {f : Fin n} →
        (g : Vec (Term {j} Σ var) (arF Σ f) → Term {i} Σ var) →
        {xs ys : Vec (Term {j} Σ var) (arF Σ f)} → 
        (xs ≡ ys) →
        (g xs) ≡ (g ys)
    zap g refl = refl


    -- {-# NO_TERMINATION_CHECK #-}
    -- mutual 
    foov : ∀ {i : Size} {n m l var} {Σ : Signature n m} → (x : Vec (Term {i} Σ var) l) →
      V.map (app' (σ-id {i})) x ≡ x
    foow : ∀ {i : Size} {n m var} {Σ : Signature n m} → (t : Term {i} Σ var) →
      app' (σ-id {i}) t ≡ t

    foov [] = refl
    foov (x ∷ xs)  = cong₂ (λ x₁ x₂ → x₁ ∷ x₂) (foow x) (foov xs)

    
    foow (VNode v) = refl
    foow (FNode f xs) = cong (λ x → FNode f xs) (foov xs)


