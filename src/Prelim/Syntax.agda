module Prelim.Syntax where

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
   VNode : (v : var) → Term {i} Σ var

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

open import Relation.Unary
open import Relation.Binary.Core
open import Level

open import Data.List.Any as LAn

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

-- | A ground terms
--
GTerm : {i : Size} → {n m : ℕ} → (Σ : Signature n m) → Set
GTerm {i} Σ =  Term {i} Σ ⊥

liftGT : {i : Size} 
  {n m : ℕ} → {Σ : Signature n m} → {var : Set} →
  GTerm {i} Σ → Term {i} Σ var
liftGT (FNode f x) = FNode f (V.map liftGT x)
liftGT (VNode ())

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

-- | A logic program
--
record Program {n m : ℕ} (Σ : Signature n m) (var : Set) : Set where
  field
    prg : List (P.Σ (CH Σ var) NoExistCH)

open Program


-- omited for now

record Subst {i : Size} {n m : ℕ} (Σ : Signature n m) (var : Set) : Set₁ where
  field
    subst : (var → Term {i} Σ var)
open Subst

record GSubst {n m : ℕ} (Σ : Signature n m) (var : Set) : Set₁ where
  field
    gsubst : Subst Σ var
    wGsubst : {x : var} →  Empty (fvT (subst gsubst x))
open GSubst

σ-id : {i : Size} {n m : ℕ} {Σ : Signature n m} {var : Set} →
  Subst {i} Σ var
σ-id = record { subst = λ x → VNode x }

σ-const : {n m : ℕ} {Σ : Signature n m} {var : Set} →
  Term Σ var → Subst Σ var
σ-const t = record { subst = λ x → t }

open import Agda.Builtin.Size

-- | substitution application
app : {i j : Size} {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → Subst {i} Σ var → Term {j} Σ var → Term Σ var
app σ (FNode {k} f fs) = FNode f (V.map (app σ) fs) 
app σ (VNode v) = subst σ v

-- | substitution application
app' : {i j :  Size}  →
  {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  → Subst {i} Σ var → Term {j} Σ var → Term {i ⊔ˢ j} Σ var
app' {i} {j} σ (FNode {k} f fs) = FNode f fs
  -- FNode {k ⊔ˢ i} f (V.map (app {i} {k} σ) fs) 
app' {i} {j} σ (VNode v) = subst σ v




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


--
-- σ-id is identity over a term
--
{-
lemma-σ-id-tvec : ∀ {i : Size} {n m l var} {Σ : Signature n m} → (x : Vec (Term {i} Σ var) l) →
V.map (app (σ-id {i})) x ≡ x

--
-- σ-id is identity over a vector of terms
-- 
lemma-σ-id-term : ∀ {i : Size} {n m var} {Σ : Signature n m} → (t : Term {i} Σ var) →
app (σ-id {i}) t ≡ t


lemma-σ-id-tvec [] = refl
lemma-σ-id-tvec (x ∷ xs)  = cong₂ (λ x₁ x₂ → x₁ ∷ x₂) (lemma-σ-id-term x) (lemma-σ-id-tvec xs)

    
lemma-σ-id-term (VNode v) = refl
lemma-σ-id-term (FNode f xs) = cong (λ x → FNode f x) (lemma-σ-id-tvec xs)
-}
    
--
-- σ-id is identity over a term
--
-- TODO size types, postulated for now
--
postulate lemma-σ-id-atom : ∀ {i : Size} {n m var} {Σ : Signature n m} → (A : At Σ var) → {-
-}  (appA σ-id) A ≡ A
--lemma-σ-id-atom (PNode p x) = cong (λ x′ → PNode p x′) (lemma-σ-id-tvec x )



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


-- A first-order proof-term signature
record PTSignature (n : ℕ) : Set where
  
open PTSignature public

-- | A first-order term
--   in a signature Σ and variables var
--
data PTerm -- {i : Size}
  {n : ℕ}
  (PTΣ : PTSignature n) (var : Set) : Set where
   AxNode :
     (f : Fin n) →
     PTerm {- i -} PTΣ var
   AppNode : -- {j k : Size< i} →
     (PTerm {-k-} PTΣ var) →
     PTerm {-j-} PTΣ var →
     PTerm {-i-} PTΣ var
   PVNode :  (v : var) → PTerm {-i-} PTΣ var
   LamNode : -- {j : Size< i} →
     List var → PTerm {-j-} PTΣ var → PTerm {-i-} PTΣ var
   MuNode : -- {j : Size< i} →
     var → PTerm {-j-} PTΣ var → PTerm {-i-} PTΣ var


-- helpers
_~_ : {n : ℕ} → {PTΣ : PTSignature n } → {var : Set} →
  PTerm PTΣ var → PTerm PTΣ var → PTerm PTΣ var
x ~ y = AppNode x y

λ'_∘_ : {n : ℕ} → {PTΣ : PTSignature n } → {var : Set} →
  List var → PTerm PTΣ var → PTerm PTΣ var
λ' x ∘ y = LamNode x y

ν_∘_ : {n : ℕ} → {PTΣ : PTSignature n } → {var : Set} →
  var → PTerm PTΣ var → PTerm PTΣ var
ν x ∘ y = MuNode x y

ptApp : {n : ℕ} → {PTΣ : PTSignature n} → {var : Set} →
  PTerm PTΣ var → List (PTerm PTΣ var) → PTerm PTΣ var
ptApp t [] = t
ptApp t (x ∷ xs) = ptApp (AppNode t x) xs

-- ptApp (AxNode κ) t₁ ∷ t₂ ∷ ... = ((AppNode (AppNode (AxNode κ) t₁) t₂) ... )

