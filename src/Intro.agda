module Intro where

open import Prelim.Syntax
open import Prelim.Res

open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Data.List


-- TODO factor out helper
-- helper
_,'_ : {A : Set} → A → A → Vec A 2
x ,' y = x ∷ (y ∷ [])

module Ex₁ where

  -- Example 1
  --
  -- Assume the following Haskell definition:
  --
  -- class Eq x where
  --   eq : : Eq x ⇒ x → x → Bool
  --
  -- instance ( Eq x , Eq y ) ⇒ Eq (x , y ) where
  --   eq ( x1 , y1 ) ( x2 , y2 ) = eq x1 x2 && eq y1 y2
  --
  -- instance Eq Int where
  --   eq x y = primtiveIntEq x y
  --
  --
  -- The signature of Φ_Pair has 2 function and 1 predicate symbols
  --
  -- Function symbols
  --   pair ≡ zero
  --   int  ≡ suc zero
  --
  -- A predicate symbol
  --   eq ≡ zero
  
  Σ_Pair : Signature 2 1
  Σ_Pair = record
    { arF = (λ { zero → 2 ; (suc zero) → 0 ; (suc (suc ())) })
    ; arP = λ { zero → 1 ; (suc ()) }
    }

  X Y : Term Σ_Pair ℕ
  X = VNode 0
  Y = VNode 1

  pair : Vec (Term Σ_Pair ℕ) 2 → Term Σ_Pair ℕ
  pair x = FNode zero x

  eq : Term Σ_Pair ℕ → At Σ_Pair ℕ
  eq t = PNode zero (t ∷ [])

  int : Term Σ_Pair ℕ
  int = FNode (suc zero) []

  open import Data.Product
  open import Data.List.Any
  open import Relation.Binary.Core as RB hiding ( _⇒_ )

  -- The program P_Pair that corresponds to above Haskell
  -- definition:
  --
  -- eq(X), eq(Y) ⇒ eq(pair(X,Y))
  --              ⇒ eq(int)
  --
  P_Pair : Program Σ_Pair ℕ
  P_Pair = record { prg
    = ((eq X ∷ eq Y ∷ []) ⇒ eq (pair (X ,' Y)) , record { noExist = λ 
           { {zero} (here (here refl)) → here (here refl)
           ; {zero} (here (there ()))
           ; {zero} (there (here (here ())))
           ; {zero} (there (here (there ())))
           ; {zero} (there (there ()))
           ; {suc zero} (here (here ()))
           ; {suc zero} (here (there ()))
           ; {suc zero} (there (here (here refl))) → here (there (here refl))
           ; {suc zero} (there (here (there ())))
           ; {suc zero} (there (there ()))
           ; {suc (suc x)} (here (here ()))
           ; {suc (suc x)} (here (there ()))
           ; {suc (suc x)} (there (here (here ())))
           ; {suc (suc x)} (there (here (there ())))
           ; {suc (suc x)} (there (there ()))
           } })
    ∷ (([] ⇒ eq int) , (record { noExist = λ { () } })) --  
    ∷ []
    }
    
  PTΣ_Pair : PTSignature 2
  PTΣ_Pair = record {}

  κ₁ κ₂ : PTerm PTΣ_Pair ℕ
  κ₁ = AxNode zero
  κ₂ = AxNode (suc zero)

  -- And corresponding axiom environment Φ_Pair
  -- 
  -- κ₁ : eq(X), eq(Y) ⇒ eq(pair(X,Y))
  -- κ₂ :              ⇒ eq(int)
  --
  Φ_Pair : AxEnv Σ_Pair ℕ PTΣ_Pair ℕ
  Φ_Pair = (·
            , κ₁ ∷ (eq X ∷ eq Y ∷ []) ⇒ eq (pair (X ,' Y))
              ⟦ record { noExist = λ
                { {zero} (here (here refl)) → here (here refl)
                ; {zero} (here (there ()))
                ; {zero} (there (here (here ())))
                ; {zero} (there (here (there ())))
                ; {zero} (there (there ()))
                ; {suc zero} (here (here ()))
                ; {suc zero} (here (there ()))
                ; {suc zero} (there (here (here refl))) → here (there (here refl))
                ; {suc zero} (there (here (there ())))
                ; {suc zero} (there (there ()))
                ; {suc (suc x)} (here (here ()))
                ; {suc (suc x)} (here (there ()))
                ; {suc (suc x)} (there (here (here ())))
                ; {suc (suc x)} (there (here (there ())))
                ; {suc (suc x)} (there (there ())) } } ⟧)
            , κ₂ ∷ [] ⇒ eq int
              ⟦ record { noExist = λ { () } } ⟧


module Ex₂ where

  -- Example 2
  --
  -- Assume the following Haskell definiton
  -- 
  -- data OddList a   = OCons a ( EvenList a )
  -- data EvenList a  = Nil | ECons a ( OddList a )
  --
  -- instance ( Eq a , Eq ( EvenList a ) ) ⇒ Eq ( OddList a ) where
  --   eq ( OCons x xs ) ( OCons y ys ) = eq x y && eq xs ys
  --
  -- instance ( Eq a , Eq ( OddList a ) ) ⇒ Eq ( EvenList a ) where
  --   eq Nil            Nil            = True
  --   eq ( ECons x xs ) ( ECons y ys ) = eq x y &&
  --   eq _               _             = False
  -- 
  -- 
  -- The signature of Φ_EvenOdd has 3 function and 1 predicate symbols
  --
  -- Function symbols
  --   evenList ≡ zero
  --   oddList  ≡ suc zero
  --   int      ≡ suc (suc zero)
  --
  -- A predicate symbol
  --   eq ≡ zero

  Σ_EvenOdd : Signature 3 1
  Σ_EvenOdd = record
    { arF = (λ
      { zero → 1
      ; (suc zero) → 1
      ; (suc (suc zero)) → 0
      ; (suc (suc (suc ()))) })
    ; arP = λ { zero → 1 ; (suc ()) }
    }


  X : Term Σ_EvenOdd ℕ
  X = VNode 0

  evenList oddList : (Term Σ_EvenOdd ℕ) → Term Σ_EvenOdd ℕ
  evenList x = FNode zero (x ∷ [])
  oddList  x = FNode (suc zero) (x ∷ [])


  eq : Term Σ_EvenOdd ℕ → At Σ_EvenOdd ℕ
  eq t = PNode zero (t ∷ [])


  int : Term Σ_EvenOdd ℕ
  int = FNode (suc (suc zero)) []

  open import Data.Product
  open import Data.List.Any
  open import Relation.Binary.Core as RB hiding ( _⇒_ )  

  -- The program P_EvenOdd that corresponds to the above Haskell definition:
  --
  -- eq(X), eq(evenList(X)) ⇒ eq(oddList(X))
  -- eq(X), eq(oddList(X))  ⇒ eq(evenList(X))
  --                        ⇒ eq(int)
  
  P_EvenOdd : Program Σ_EvenOdd ℕ
  P_EvenOdd = record { prg
    = (((((eq X) ∷ (eq (evenList X)) ∷ []) ⇒ eq (oddList X))
      , record { noExist = λ
        { {.zero} (here (here refl)) → here (here refl)
        ; {_} (here (there ()))
        ; {.zero} (there (here (here (here refl)))) → here (here refl)
        ; {_} (there (here (here (there ()))))
        ; {_} (there (here (there ())))
        ; {_} (there (there ()))
        } } ))
    ∷ ((((eq X) ∷ (eq (oddList X)) ∷ []) ⇒ eq (evenList X))
      , record { noExist = λ
        { {.zero} (here (here refl)) → here (here refl)
        ; {_} (here (there ()))
        ; {.zero} (there (here (here (here refl)))) → here (here refl)
        ; {_} (there (here (here (there ()))))
        ; {_} (there (here (there ())))
        ; {_} (there (there ()))
        } } )
    ∷ (([] ⇒ eq int)
      , record { noExist = λ { () } })
    ∷ []
    }

  PTΣ_EvenOdd : PTSignature 3
  PTΣ_EvenOdd = record {}

  κ₁ κ₂ κ₃ : PTerm PTΣ_EvenOdd ℕ
  κ₁ = AxNode zero
  κ₂ = AxNode (suc zero)
  κ₃ = AxNode (suc (suc zero))

  open import Data.List.Any
  open import Relation.Binary.Core as RB hiding ( _⇒_ )

  -- Abd the correspondign axiom environment  Φ_EvenOdd
  --
  -- κ₁ : eq(X), eq(evenList(X)) ⇒ eq(oddList(X))
  -- κ₂ : eq(X), eq(oddList(X))  ⇒ eq(evenList(X))
  -- κ₃ :                        ⇒ eq(int)
  --
  Φ_EvenOdd : AxEnv Σ_EvenOdd ℕ PTΣ_EvenOdd ℕ
  Φ_EvenOdd = ((·
              , κ₁ ∷ (eq X ∷ eq (evenList X) ∷ []) ⇒ eq (oddList X)
                ⟦ record { noExist = λ
                  { {.zero} (here (here refl)) → here (here refl)
                  ; {_} (here (there ()))
                  ; {.zero} (there (here (here (here refl)))) → here (here refl)
                  ; {_} (there (here (here (there ()))))
                  ; {_} (there (here (there ())))
                  ; {_} (there (there ()))
                  }} ⟧)
              , κ₂ ∷ (eq X ∷ eq (oddList X) ∷ []) ⇒ eq (evenList X)
                ⟦ record { noExist = λ
                  { {.zero} (here (here refl)) → here (here refl)
                  ; {_} (here (there ()))
                  ; {.zero} (there (here (here (here refl)))) → here (here refl)
                  ; {_} (there (here (here (there ()))))
                  ; {_} (there (here (there ())))
                  ; {_} (there (there ()))
                  }} ⟧)
              , κ₃ ∷ [] ⇒ eq int
                ⟦ record { noExist = λ { () } } ⟧
                
-- Example 3
--
-- Φ_Bush =
-- κ₁ : ⇒ eq(int)
-- κ₂ : eq(X), eq(bush(bush(X)) ⇒ eq(bush(X))

