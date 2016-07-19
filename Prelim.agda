module Prelim where

open import Data.Nat
open import Data.Fin

-- A first-order signature
record Signature (n : ℕ) (m : ℕ) : Set where
  field
    -- function symbols are encoded as numbers in Fin n
    -- predicate symbpols as numbers in Fin m
    -- arities
    arF : Fin n → ℕ
    arP : Fin m → ℕ

open Signature public


-- | A countable set of variables
V : Set
V = ℕ

open import Data.Vec as V
open import Size

-- | A first-order term
--   in a signature Σ and variables var
--
data Term {i : Size}
  {n m : ℕ}
  (Σ : Signature n m) (var : Set) : Set where
   FNode : {j : Size< i} →
     (f : Fin n) → Vec (Term {j} Σ var) (arF Σ f)
     → Term {i} Σ var
   VNode :  (v : var) → Term {i} Σ var

-- | An atomic formula
--
data At
  {n m : ℕ}
  (Σ : Signature n m) (var : Set) : Set where
  PNode :
    (p : Fin m) → Vec (Term Σ var) (arP Σ p)
    → At Σ var

open import Data.List

-- | A Horn formula
--
data CH
  {n m : ℕ}
  (Σ : Signature n m) (var : Set) : Set where
  _⇒_ : List (At Σ var) → At Σ var → CH Σ var

chH : {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  CH Σ var → At Σ var
chH (_ ⇒ h) = h

chB : {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  CH Σ var → List (At Σ var)
chB (bs ⇒ _) = bs

open import Relation.Unary hiding (U)
open import Relation.Binary.Core
open import Level

open import Data.List.Any
open import Data.Vec
--open import Data.List.Any.Properties as AP


fvT : {i : Size}
  → {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → Term {i} Σ var → Pred var Level.zero
fvT (FNode f x) y = Any ( λ x' → fvT x' y) (toList x)
fvT (VNode v) y = v ≡ y

fvAt : {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → At Σ var → Pred var Level.zero
fvAt (PNode p x) y = Any (λ x' → fvT x' y) (toList x)

fvB : {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → List (At Σ var) → Pred var Level.zero
fvB x y = Any (λ x' → fvAt x' y) x

-- A certificate that there are no existential variables in a HC
record NoExistCH 
  {n m : ℕ}
  {Σ : Signature n m} {var : Set}
  (fla : CH Σ var) : Set where
  field
    noExist : fvB (chB fla) ⊆ fvAt (chH fla)
    
open NoExistCH

open import Data.Empty
open import Data.Vec as V

-- | A ground terms
--
GTerm : {i : Size} → {n m : ℕ} → (Σ : Signature n m) → Set
GTerm {i} Σ =  Term {i} Σ ⊥

liftGT : {i : Size} 
  {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  GTerm {i} Σ → Term {i} Σ var
liftGT (FNode f x) = FNode f (V.map liftGT x)
liftGT (VNode ())

open import Data.List.Any as LAn
open import Data.Product as P

myMap : {A : Set} → {B : Set} → {n : ℕ} →
  (v : Vec A n) →
  (P.Σ A (λ a → Any (λ x → x ≡ a) (toList v)) → B) →
  (Vec B n)
myMap [] x = []
myMap (x ∷ v) f = f (x , here refl) ∷ myMap v (λ {
  (a , wA) → f (a , there wA)
  })

dropGT : {i : Size} 
  {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  (t : Term {i} Σ var)
  → Empty (fvT t)
  → GTerm {i} Σ
dropGT {i} {n} {m} {Σ} {var}
  (FNode f x) wEq = FNode f (myMap x (λ {
    (y , wY) → dropGT y (λ
      v x₂ → wEq v (LAn.map (λ {x} x₃ → baz y v x₂ x x₃) wY)
    ) }))
    where

      baz : {j : Size< i } →
          (y    : Term {j} Σ var) → (v    : var) →
          (v Relation.Unary.∈ fvT y) →
          (x    : Term {j} Σ var) →
          (x₂   : x Relation.Unary.∈ (λ z → z ≡ y)) →
          (x Relation.Unary.∈ (λ x' → fvT x' v))
      baz y v wY .y refl = wY

dropGT (VNode v) wEq with wEq v refl
dropGT (VNode v) wEq | ()

open import Data.Vec as V
open import Data.Unit


-- | A ground atom
--
GAt : {n m : ℕ} → (Σ : Signature n m) → Set
GAt Σ = At Σ ⊥

liftGAt : {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  GAt Σ → At Σ var
liftGAt (PNode p x) = PNode p (V.map liftGT x)

dropGAt :
  {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  (at : At Σ var)
  → Empty (fvAt at)
  → GAt  Σ
dropGAt {n} {m} {Σ} {var} (PNode p x) wE = PNode p
  (myMap x (λ {
    (t , wT) → dropGT t (λ v wV → wE v (LAn.map (λ {x} x₃
      → foo t wT v wV x x₃) wT))
   }))
   where
     foo : (t    : Term Σ var) →
       (wT   : Any (λ x₁ → x₁ ≡ t) (toList x)) →
       (v    : var) →
       (v Relation.Unary.∈ fvT t) →
       (x    : Term Σ var) →
       (x Relation.Unary.∈ (λ x₁ → x₁ ≡ t)) →
       (x Relation.Unary.∈ (λ x₁ → fvT x₁ v))
     foo t wT v wV .t refl = wV

-- | A ground Horn formula
--
GCH : {n m : ℕ} → (Σ : Signature n m) → Set
GCH Σ = CH Σ ⊥


open import Data.Product as P

-- | A logic program
--
record Program {n m : ℕ} (Σ : Signature n m) (var : Set) : Set where
  field
    prg : List (P.Σ (CH Σ var) NoExistCH)

open Program


-- omited for now

record Subst {n m : ℕ} (Σ : Signature n m) (var : Set) : Set₁ where
  field
    subst : (var → Term Σ var)
open Subst

record GSubst {n m : ℕ} (Σ : Signature n m) (var : Set) : Set₁ where
  field
    gsubst : Subst Σ var
    wGsubst : {x : var} →  Empty (fvT (subst gsubst x))
open GSubst

σ-id : {n m : ℕ} {Σ : Signature n m} {var : Set} →
  Subst Σ var
σ-id = record { subst = λ x → VNode x }

σ-const : {n m : ℕ} {Σ : Signature n m} {var : Set} →
  Term Σ var → Subst Σ var
σ-const t = record { subst = λ x → t }

-- | substitution application
app : {i : Size} →
  {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → Subst Σ var → Term {i} Σ var → Term Σ var
app σ (FNode f fs) = FNode f (V.map (app σ) fs)
app σ (VNode v) = subst σ v

-- | ground substitution application
gApp : {i : Size} →
  {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → GSubst Σ var → Term {i} Σ var → GTerm Σ
gApp σ (FNode f x) = FNode f (V.map (gApp σ) x)
gApp σ (VNode v) = dropGT (subst (gsubst σ) v) (wGsubst σ)

appA : {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → Subst Σ var → At Σ var → At Σ var
appA σ (PNode p x) = PNode p (V.map (app σ) x)

gAppA : {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → GSubst Σ var → At Σ var → GAt Σ
gAppA σ (PNode p x) = PNode p (V.map (gApp σ) x)

open import Data.List as Ls
open import Data.List.All

record AtIsGInstOf {n m : ℕ} {Σ : Signature n m} {var : Set}
  (gat : GAt Σ) (at : At Σ var) : Set₁ where
  field
    s   : GSubst Σ var
    eq :  gat ≡ gAppA s at
open AtIsGInstOf

record CHIsGInstOf {n m : ℕ} {Σ : Signature n m} {var : Set}
  (gch : GCH Σ) (ch : CH Σ var) : Set₁ where
  field
    s' : (Subst Σ var)
    eqH : AtIsGInstOf (chH gch) (chH ch)
    eqB : All ( λ { (gcb , cb) → AtIsGInstOf gcb cb })
      (Ls.zip (chB gch) (chB ch))
open CHIsGInstOf

open import Data.List.All.Properties

open NoExistCH

open import Data.List.All as LA

{-

-- A first-order proof-term signature
record PTSignature (n : ℕ) : Set where
  
open PTSignature public

-- | A first-order term
--   in a signature Σ and variables var
--
data PTerm {i : Size}
  {n : ℕ}
  (PTΣ : PTSignature n) (var : Set) : Set where
   AxNode : {j : Size< i} →
     (f : Fin n) --  → Vec (PTerm {j} PTΣ var) (arF Σ f)
     → PTerm {i} PTΣ var
   AppNode : {j : Size< i} → (f : Fin n) →
     PTerm {j} PTΣ var →
     PTerm {i} PTΣ var
   PVNode :  (v : var) → PTerm {i} PTΣ var
   LamNode : List var → PTerm {i} PTΣ var → PTerm {i} PTΣ var
   MuNode : var → PTerm {i} PTΣ var → PTerm {i} PTΣ var

-- helpers
--_~_ : {n : ℕ} → {PTΣ : PTSignature n } → {var : Set} →
--  PTerm PTΣ var → PTerm PTΣ var → PTerm PTΣ var
--x ~ y = AppNode x y

λ'_∘_ : {n : ℕ} → {PTΣ : PTSignature n } → {var : Set} →
  List var → PTerm PTΣ var → PTerm PTΣ var
λ' x ∘ y = LamNode x y

μ_∘_ : {n : ℕ} → {PTΣ : PTSignature n } → {var : Set} →
  var → PTerm PTΣ var → PTerm PTΣ var
μ x ∘ y = MuNode x y

{-
ptHead : {n : ℕ} → {PTΣ : PTSignature n } → {var : Set} →
  (pt : PTerm PTΣ var) → (pt ≡ {!AxNode!}) → PTerm PTΣ var
ptHead = {!!}
-}

data AxEnv {n m l : ℕ}
  (Σ : Signature n m) (var : Set)
  (PTΣ : PTSignature l) (pVar : Set) : Set where

  · : AxEnv Σ var PTΣ pVar
  _,_∷_⟦_⟧  : AxEnv Σ var PTΣ pVar →
    PTerm PTΣ pVar →
    (ch : CH Σ var) →
    NoExistCH ch  →
    AxEnv Σ var PTΣ pVar
  
----


-- Herbrand Universe

U : {n m : ℕ} → (Σ : Signature n m) → Set
U Σ = GTerm Σ

-- Herbrand Base

B : {n m : ℕ} → (Σ : Signature n m) → Set
B Σ = GAt Σ

-- Semantic operator

open import Level as L

open Program

{-
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
    { s' = s wGh
    ; eqH = wGh
    ; eqB = []
    })
foo gh ((chb₁ ∷ chb) CH.⇒ h) neCh wGh
  with foo gh (chb CH.⇒ h) (record
    { noExist = λ { {v} y → noExist neCh (there y) } })
    wGh 
...| (gchb CH.⇒ _ , wGch )
  = ((appA (s wGh) chb₁ ∷ gchb ) CH.⇒ gh)
  , record
    { s' = s wGh
    ; eqH = wGh
    ; eqB = (record
      { s = s wGh
      ; eq = refl
      }) ∷ eqB wGch }

open import Data.Sum
open import Data.Unit
open import Data.Fin as F

{-
bar : {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  (gh : GAt Σ) →
  ( h : At Σ var) →

  (AtIsGInstOf gh h ⊎ ⊤)
bar (PNode p x) (PNode q y) with F.compare p q
bar (PNode .(inject least) x) (PNode greatest y) | less .greatest least = inj₂ tt
bar (PNode p x) (PNode .p y) | equal .p = inj₁ (record
  { s = {!!}
  ; eq = {!!} })
bar (PNode p x) (PNode .(inject least) y) | greater .p least = inj₂ tt
-}

{-
open GSubst
open import Data.Maybe
open import Data.Bool as B

lem-gterm-comp : {n m l : ℕ} → (Σ : Signature n m) → (var : Set) →
  (gt₁   : Vec (GTerm Σ) l) →
  (gt₂   : Vec (GTerm Σ) l) →
  Bool
lem-gterm-comp Σ var [] [] = true
lem-gterm-comp Σ var (FNode f x ∷ gts₁) (FNode g y ∷ gts₂) with F.compare f g
lem-gterm-comp Σ var (FNode .(inject least) x ∷ gts₁) (FNode greatest y ∷ gts₂) | less .greatest least = false
lem-gterm-comp Σ var (FNode f x ∷ gts₁) (FNode .f y ∷ gts₂) | equal .f = lem-gterm-comp Σ var x y ∧ lem-gterm-comp Σ var gts₁ gts₂
lem-gterm-comp Σ var (FNode f x ∷ gts₁) (FNode .(inject least) y ∷ gts₂) | greater .f least = false
lem-gterm-comp Σ var (FNode _ _ ∷ gts₁) (VNode () ∷ gts₂)
lem-gterm-comp Σ var (VNode () ∷ gts₁) (_ ∷ gts₂)
-}



{-
compS : {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  GSubst Σ var → GSubst Σ var → GSubst Σ var

compS s₁ s₂ with subst s₁ | subst s₂
...| σ₁ | σ₂ = record { subst = λ { x  → {!!} } }
-}

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

open import Relation.Unary as RU

record AtValid {n m : ℕ} {Σ : Signature n m} {var : Set}
  (I : Pred (B Σ) L.zero) (at : At Σ var) : Set₁ where
  field
    wVal : ∀ {σ : Subst Σ var} →
      (appA σ at RU.∈ I)
      
record CHValid {n m : ℕ} {Σ : Signature n m} {var : Set}
  (I : Pred (GAt Σ) L.zero) (ch : CH Σ var) : Set₁ where
  field
    wVal : ∀ {σ : Subst Σ var} →
      All (λ t → AtValid I (appA σ t)) (chB ch) --(toList (chB ch) →
      → AtValid I (appA σ (chH ch))

open import Data.List.Any as LAn

--
-- Lemma 1, inductive part
--
-- a/
postulate lemma-1-a-i  : {n m : ℕ} {Σ : Signature n m} {var : Set} {P : Program Σ var} {A : At Σ var} → Any  ( λ { (ch , _) → ch ≡ [] CH.⇒ A }) (prg P) → AtValid (fp (lfp (M P))) A




-- Type class resolution

data _⊢_∷_ {n m l : ℕ} {Σ : Signature n m} {var : Set}
  {PTΣ : PTSignature l} {pVar : Set}
  (Φ : AxEnv Σ var PTΣ pVar)
  (pt : PTerm PTΣ pVar)
  (ch : CH Σ var)
  : Set where

  Lp-m : {σ : Subst} →
    List (? × ?) →
    {!!} → All {!!} (chB ch) → Φ ⊢ {!!} ∷ {!!}

-}

-}
