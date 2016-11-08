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

      (eᵢs : List (PTerm PTΣ pVar))
      (κ : Fin l ) → -- ^ axiom of PTΣ
      (wCh : H ≡ [] ⇒ A)
      (wPt : pt ≡ MuNode α (ptApp (AxNode κ) eᵢs)) →
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



  open import Data.List.All.Properties
  open import Relation.Binary.PropositionalEquality


  lemma-AppNode :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set} → (H e : PTerm PTΣ pVar)
    → (es : List (PTerm PTΣ pVar)) → P.Σ (PTerm PTΣ pVar) (λ e'
      → Σ (PTerm PTΣ pVar) (λ e''  → ptApp H (e ∷ es) ≡ AppNode e' e'')) 
  lemma-AppNode H e [] = H , (e , refl)
  lemma-AppNode H e (d ∷ es) = P.map (λ x → x) (λ x₁ → x₁) (lemma-AppNode (AppNode H e) d es)


  lemma-AppNode-eqcomp :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (e₁ d₁ e₂ d₂ : PTerm PTΣ pVar)
    → AppNode e₁ d₁ ≡ AppNode e₂ d₂
    → e₁ ≡ e₂ × d₁ ≡ d₂
  lemma-AppNode-eqcomp (AxNode f) d₁ (AxNode .f) .d₁ refl = refl , refl
  lemma-AppNode-eqcomp (AxNode f) d₁ (AppNode e₂ e₃) d₂ ()
  lemma-AppNode-eqcomp (AxNode f) d₁ (PVNode v) d₂ ()
  lemma-AppNode-eqcomp (AxNode f) d₁ (LamNode x e₂) d₂ ()
  lemma-AppNode-eqcomp (AxNode f) d₁ (MuNode x e₂) d₂ ()
  lemma-AppNode-eqcomp (AppNode e₁ e₂) d₁ (AxNode f) d₂ ()
  lemma-AppNode-eqcomp (AppNode e₁ e₂) d₁ (AppNode .e₁ .e₂) .d₁ refl = refl , refl
  lemma-AppNode-eqcomp (AppNode e₁ e₂) d₁ (PVNode v) d₂ ()
  lemma-AppNode-eqcomp (AppNode e₁ e₂) d₁ (LamNode x e₃) d₂ ()
  lemma-AppNode-eqcomp (AppNode e₁ e₂) d₁ (MuNode x e₃) d₂ ()
  lemma-AppNode-eqcomp (PVNode v) d₁ (AxNode f) d₂ ()
  lemma-AppNode-eqcomp (PVNode v) d₁ (AppNode e₂ e₃) d₂ ()
  lemma-AppNode-eqcomp (PVNode v) d₁ (PVNode .v) .d₁ refl = refl , refl
  lemma-AppNode-eqcomp (PVNode v) d₁ (LamNode x e₂) d₂ ()
  lemma-AppNode-eqcomp (PVNode v) d₁ (MuNode x e₂) d₂ ()
  lemma-AppNode-eqcomp (LamNode x e₁) d₁ .(LamNode x e₁) .d₁ refl = refl , refl
  lemma-AppNode-eqcomp (MuNode x e₁) d₁ (AxNode f) d₂ ()
  lemma-AppNode-eqcomp (MuNode x e₁) d₁ (AppNode e₂ e₃) d₂ ()
  lemma-AppNode-eqcomp (MuNode x e₁) d₁ (PVNode v) d₂ ()
  lemma-AppNode-eqcomp (MuNode x e₁) d₁ (LamNode x₁ e₂) d₂ ()
  lemma-AppNode-eqcomp (MuNode x e₁) d₁ (MuNode .x .e₁) .d₁ refl = refl , refl


  head-symbol :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (t : PTerm {-i-} PTΣ pVar)
    → PTerm {-j-} PTΣ pVar
  head-symbol (AxNode f) = AxNode f
  head-symbol (AppNode t t₁) = head-symbol t
  head-symbol (PVNode v) = PVNode v
  head-symbol (LamNode x t) = LamNode x t
  head-symbol (MuNode x t) =  MuNode x t

  lemma-AppNode4 :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (H : PTerm PTΣ pVar) 
    → (es : List (PTerm PTΣ pVar))
    →  head-symbol (ptApp (H) es) ≡ head-symbol H
  lemma-AppNode4 H [] = refl
  lemma-AppNode4 H (x ∷ es) = lemma-AppNode4 (AppNode H x) es


  lemma-AppNode2 :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (H₁ H₂ : PTerm PTΣ pVar)
    → (es₁ es₂ : List (PTerm PTΣ pVar))
    →  ptApp (H₁) es₁ ≡ ptApp (H₂) es₂
    → head-symbol H₁ ≡ head-symbol H₂
  lemma-AppNode2 (H₁) H₂ es₁ es₂ w with lemma-AppNode4 H₁ es₁ | lemma-AppNode4 H₂ es₂ | cong head-symbol w
  ... | z | y | x = trans (sym z) (trans x y)
  
  lemma-ptApp-headl :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (H : PTerm PTΣ pVar)
    → {x y : PTerm PTΣ pVar}
    → AppNode x y ≡ head-symbol H
    → ⊥
  lemma-ptApp-headl (AxNode f) ()
  lemma-ptApp-headl (AppNode H₁ H₂) w = lemma-ptApp-headl H₁ w
  lemma-ptApp-headl (PVNode v) ()
  lemma-ptApp-headl (LamNode x H) ()
  lemma-ptApp-headl (MuNode x H) ()

  lemma-ptApp-head :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → {H I x  : PTerm PTΣ pVar}
    → (es : List (PTerm PTΣ pVar))
    → I ≡ ptApp (AppNode H x) es
    → I ≡ head-symbol I
    → ⊥
  lemma-ptApp-head {H = AxNode f} [] refl ()
  lemma-ptApp-head {H = AppNode H₁ H₂} [] refl w₂ = lemma-ptApp-headl H₁ w₂
  lemma-ptApp-head {H = PVNode v} [] refl ()
  lemma-ptApp-head {H = LamNode x H} [] refl ()
  lemma-ptApp-head {H = MuNode x H} [] refl ()
  lemma-ptApp-head (x₁ ∷ es) refl x₃ = lemma-ptApp-head es refl x₃

  lemma-list-tail :
    {A : Set}
    → (x : A)
    → (xs : List A)
    → Σ (List A) (λ ys → Σ A (λ y → x ∷ xs ≡ ys L.++ y ∷ []))
  lemma-list-tail x [] = [] , x , refl
  lemma-list-tail x (x₁ ∷ xs) = P.map (λ x₂ → x ∷ x₂) (λ { {zs} (y , w) → y , cong (λ x₂ → x ∷ x₂) w }) (lemma-list-tail x₁ xs)

  lemma-ptApp-eql2 :
    {A : Set}
    {z : A}
    → (zs : List A)
    → [] ≡ zs L.++ z ∷ []
    → ⊥
  lemma-ptApp-eql2 [] ()
  lemma-ptApp-eql2 (x ∷ zs) ()

  open import Data.List.Properties
  lemma-ptApp-eql :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (H x z : PTerm PTΣ pVar)
    → (es zs : List (PTerm PTΣ pVar))
    → (x ∷ es ≡ zs L.++ z ∷ [])
    → ptApp (AppNode H x) es ≡ AppNode (ptApp H zs) z
  lemma-ptApp-eql H x .x [] [] refl = refl
  lemma-ptApp-eql H x z [] (x₁ ∷ zs) w with ∷-injective w
  lemma-ptApp-eql H x z [] (.x ∷ zs) w | refl , w₂ = ⊥-elim (lemma-ptApp-eql2 zs w₂)
  lemma-ptApp-eql H x z (x₁ ∷ es) [] w with ∷-injective w
  lemma-ptApp-eql H x .x (x₁ ∷ es) [] w | refl , ()
  lemma-ptApp-eql H x z (e ∷ es) (x₁ ∷ zs) w with ∷-injective w 
  lemma-ptApp-eql H x z (e ∷ es) (.x ∷ zs) w | refl , w₂ = lemma-ptApp-eql (AppNode H x) e z es zs w₂

  lemma-ptApp-subl :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (H H₁ : PTerm PTΣ pVar)
    → H ≡ AppNode H H₁ 
    → ⊥
  lemma-ptApp-subl H H₁ ()

  lemma-ptApp-sub :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (H x  : PTerm PTΣ pVar)
    → (es : List (PTerm PTΣ pVar))
    → H ≡ ptApp (AppNode H x) es
    → ⊥
  lemma-ptApp-sub (AxNode f) x [] ()
  lemma-ptApp-sub (AppNode H H₁) x [] x₁ = lemma-ptApp-subl (AppNode H H₁) x x₁
  lemma-ptApp-sub (PVNode v) x [] ()
  lemma-ptApp-sub (LamNode x H) x₁ [] ()
  lemma-ptApp-sub (MuNode x H) x₁ [] ()
  lemma-ptApp-sub (AxNode f) x (x₁ ∷ es) x₂ = lemma-ptApp-head es x₂ refl

  lemma-ptApp-sub (AppNode H H₁) x (x₁ ∷ es) x₂ with lemma-list-tail x₁ es
  lemma-ptApp-sub (AppNode H H₁) x (x₁ ∷ es) x₂ | zs , z , w with
    trans x₂ (lemma-ptApp-eql (AppNode (AppNode H H₁) x) x₁ z es zs w)
  ... | w₁ with lemma-AppNode-eqcomp H H₁ (ptApp (AppNode (AppNode H H₁) x) zs) z w₁
  lemma-ptApp-sub (AppNode H z) x (x₁ ∷ es) x₂ | zs , .z , w | w₁ | w₂ , refl
    = lemma-ptApp-sub H z (x ∷ zs) w₂
  lemma-ptApp-sub (PVNode v) x (x₁ ∷ es) x₂ = lemma-ptApp-head es x₂ refl
  lemma-ptApp-sub (LamNode x H) x₁ (x₂ ∷ es) x₃ = lemma-ptApp-head es x₃ refl
  lemma-ptApp-sub (MuNode x H) x₁ (x₂ ∷ es) x₃ = lemma-ptApp-head es x₃ refl


  {-# TERMINATING #-}
  {- length zs₁ ≡ length eq₁ ; length zs₂ ≡ length eq₁ -}
  lemma-ptApp-eq :
    {n : ℕ} {PTΣ : PTSignature n} {pVar : Set}
    → (H : PTerm PTΣ pVar)
    → (es₁ es₂ : List (PTerm PTΣ pVar))
    → ptApp H es₁ ≡ ptApp H es₂
    → es₁ ≡ es₂
  lemma-ptApp-eq H [] [] refl = refl
  lemma-ptApp-eq H [] (x ∷ es₂) w with lemma-list-tail x es₂
  ... | zs , z , w₁ = ⊥-elim (lemma-ptApp-sub H x es₂ w)
  lemma-ptApp-eq H (x ∷ es₁) [] w = ⊥-elim (lemma-ptApp-sub H x es₁ (sym w))
  lemma-ptApp-eq H (x₁ ∷ es₁) (x₂ ∷ es₂) w with lemma-list-tail x₁ es₁ | lemma-list-tail x₂ es₂
  ... | zs₁ , z₁ , w₁ | zs₂ , z₂ , w₂ with
    lemma-ptApp-eql H x₁ z₁ es₁ zs₁ w₁ | lemma-ptApp-eql H x₂ z₂ es₂ zs₂ w₂
  ... | p | q with lemma-AppNode-eqcomp (ptApp H zs₁) z₁ (ptApp H zs₂) z₂ (trans (trans (sym p) w) q)
  lemma-ptApp-eq H (x₁ ∷ es₁) (x₂ ∷ es₂) w | zs₁ , z₁ , w₁ | zs₂ , .z₁ , w₂ | p | q | w₃ , refl with
    lemma-ptApp-eq H zs₁ zs₂ w₃
  lemma-ptApp-eq H (x₁ ∷ es₁) (x₂ ∷ es₂) w | zs₁ , z₁ , w₁ | .zs₁ , .z₁ , w₂ | p | q | w₃ , refl | refl
    = trans w₁ (sym w₂)

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

      -- thm-coind-sound made explicit
      -- ({A' : At Σ var} {e : PTerm PTΣ pVar} →
      -- Φ ⊢ e ∷ ([] ⇒ A') → toPrg Φ ⊨'' ([] ⇒ A')) →
      All (λ { (eᵢ , Bᵢ) → Φ ⊢ eᵢ ∷ ([] ⇒ appA σ Bᵢ) } )
        (toList (V.zip eᵢs Bᵢs)) →

      All (λ { Bᵢ → (toPrg Φ) ⊨coind (appA σ Bᵢ)})
        (toList  Bᵢs)


-- TODO

--} → All (λ {Bᵢ → {-
--}      extPrg P ((([] ⇒ appA σ A) , record { noExist = λ { () } }) ∷ []) {-
--}         ⊨coind appA σ Bᵢ}) Bs  {-
-- -} → (Any (λ { (ch , wCH) → ch ≡ (Bs ⇒ A) }) (prg P)) {-

  postulate lemma-3 : {n m : ℕ} {-
-} {Σ : Signature n m} {var : Set} {-
-} {Bs : List (At Σ var)} {-
-} {P : Program Σ var} {A : At Σ var} {-

-} → (σ : Subst Σ var) {-
-} → All (λ {Bᵢ → extPrg P ((([] ⇒ A) , (record { noExist = λ { () }})) ∷ []) {-
-}                ⊨coind (appA σ Bᵢ)}) Bs {-
-} → P ⊨''coind ([] CH.⇒ appA σ A)

  thm-coind-sound :
    ∀ {l m n} {Σ : Signature n m} → {var : Set}
    {PTΣ : PTSignature l} → {pVar : Set} 
    {Φ : AxEnv Σ var PTΣ pVar } →
    {A' : At Σ var} →
    {e : PTerm PTΣ pVar} →

    Φ ⊢ e ∷ ([] ⇒ A') → (toPrg Φ) ⊨''coind ([] ⇒ A')
  thm-coind-sound (Lp-m {Bᵢs = []} refl σ A refl [] refl [] wCH)
    = lemma-atohc' (lemma-1-a-c (ae2a wCH (λ
      { {ch = [] ⇒ .A} refl → refl } ))) 
  thm-coind-sound (Lp-m {Bᵢs = Bᵢs} refl σ A refl eᵢs refl wBᵢs wCH)
    = lemma-atohc' (lemma-1-b-c
                   (map-vec' wBᵢs)
                   (ae2a wCH ((λ {
                     {ch = .(toList Bᵢs) ⇒ .A} refl → refl
                   }))))
        
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = AxNode κ'} refl σ A refl eᵢs₁ wPt wBᵢs wCH))
    with lemma-AppNode2 (AxNode κ) (AxNode κ') eᵢs (toList eᵢs₁) wPt
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ' refl refl (Lp-m {n'} {Bᵢs} {AxNode .κ'} refl σ A refl eᵢs₁ wPt wBᵢs wCH)) | refl
    with lemma-ptApp-eq (AxNode κ') eᵢs (toList eᵢs₁) wPt
  thm-coind-sound (Nu' .(appA σ A) α .(toList eᵢs₁) κ' refl refl (Lp-m {n'} {Bᵢs} {AxNode .κ'} refl σ A refl eᵢs₁ refl wBᵢs wCH)) | refl | refl
    = {!!}
  
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = AppNode e e₁} refl σ A refl eᵢs₁ wPt wBᵢs wCH)) = {!!}


--  with lemma-AppNode2 (AxNode κ) (AppNode e e₁) eᵢs (toList eᵢs₁) wPt
--  ... | z = {!!}
  
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = PVNode v} refl σ A refl eᵢs₁ wPt wBᵢs wCH))
    with lemma-AppNode2 (AxNode κ) (PVNode v) eᵢs (toList eᵢs₁) wPt
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {n'} {Bᵢs} {PVNode v} refl σ A refl eᵢs₁ wPt wBᵢs wCH)) | ()
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = LamNode x e} refl σ A refl eᵢs₁ wPt wBᵢs wCH))
    with lemma-AppNode2 (AxNode κ) (LamNode x e) eᵢs (toList eᵢs₁) wPt  
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {n'} {Bᵢs} {LamNode x e} refl σ A refl eᵢs₁ wPt wBᵢs wCH)) | ()
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = MuNode x e} refl σ A refl eᵢs₁ wPt wBᵢs wCH))
    with lemma-AppNode2 (AxNode κ) (MuNode x e) eᵢs (toList eᵢs₁) wPt
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {n'} {Bᵢs} {MuNode x e} refl σ A refl eᵢs₁ wPt wBᵢs wCH)) | ()


  {- {!lemma-3 σ ? (ae2a x₂ (λ {
        {ch = .(toList Bᵢs) ⇒ .A} refl → refl
      }))!}
  -}

  {- {!ae2a x₂ ((λ {
      {ch =.(toList Bᵢs) ⇒ .A} refl → refl
      })) !}-}
    -- {!lemma-3 ? (ae2a x₂ (λ { {ch} refl → refl}))!}


  -- to show : e ≡ pt
  
{-
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = AxNode f} refl σ A refl eᵢs₁ wPt x₁ x₂)) = {!!}
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = AppNode e e₁} refl σ A refl eᵢs₁ wPt x₁ x₂))
    with lemma-AppNode4 (AxNode κ) eᵢs | lemma-AppNode4 (AppNode e e₁) (toList eᵢs₁) | cong head-symbol wPt
  ... | u | v | z with trans (sym u) (trans z v)
  ... | j = {!!}

  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = PVNode v} refl σ A refl eᵢs₁ wPt x₁ x₂))
    with lemma-AppNode4 (AxNode κ) eᵢs | lemma-AppNode4 (PVNode v) (toList eᵢs₁) | cong head-symbol wPt
  ... | u | v' | z with trans (sym u) (trans z v')
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {n'} {Bᵢs} {PVNode v} refl σ A refl eᵢs₁ wPt x₁ x₂)) | u | v' | z | ()
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = LamNode x e} refl σ A refl eᵢs₁ wPt x₁ x₂))
    with lemma-AppNode4 (AxNode κ) eᵢs | lemma-AppNode4 (LamNode x e) (toList eᵢs₁) | cong head-symbol wPt
  ... | u | v | z with trans (sym u) (trans z v)
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {n'} {Bᵢs} {LamNode x e} refl σ A refl eᵢs₁ wPt x₁ x₂)) | u | v | z | ()
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {e = MuNode x e} refl σ A refl eᵢs₁ wPt x₁ x₂))
    with lemma-AppNode4 (AxNode κ) eᵢs | lemma-AppNode4 (MuNode x e) (toList eᵢs₁) | cong head-symbol wPt
  ... | u | v | z with trans (sym u) (trans z v)
  thm-coind-sound (Nu' .(appA σ A) α eᵢs κ refl refl (Lp-m {n'} {Bᵢs} {MuNode x e} refl σ A refl eᵢs₁ wPt x₁ x₂)) | u | v | z | ()
-}

  thm-coind-sound (Nu' .(PNode p x) α [] κ refl refl (Nu' (PNode p x) α₁ eᵢs₁ κ₁ refl () x₁))
  thm-coind-sound (Nu' .(PNode p x) α (eᵢ ∷ eᵢs) κ refl refl (Nu' (PNode p x) α₁ eᵢs₁ κ₁ refl wPt x₂)) with lemma-AppNode (AxNode κ) eᵢ eᵢs
  thm-coind-sound (Nu' .(PNode p x) α (eᵢ ∷ eᵢs) κ refl refl (Nu' (PNode p x) α₁ eᵢs₁ κ₁ refl wPt x₂)) | t₁ , t₂ , w with trans (sym w) wPt
  thm-coind-sound (Nu' .(PNode p x) α (eᵢ ∷ eᵢs) κ refl refl (Nu' (PNode p x) α₁ eᵢs₁ κ₁ refl wPt x₂)) | t₁ , t₂ , w | ()
  
  map-vec' {eᵢs = []} {Bᵢs = []} {- _ -} [] = []
  map-vec' {eᵢs = _ ∷ _} {Bᵢs = _ ∷ _} {- f -} (px ∷ x)
      = lemma-chtoa' (thm-coind-sound px) ∷ (map-vec' x) 


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
