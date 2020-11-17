open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Reflection using (TC)
open import Reflection.Name using (Names)
import Reflection.TypeChecking.Monad.Categorical as RCat
open import Data.Nat using (ℕ)
open import Category.Monad.State using (State; StateT; StateMonad; StateTMonad)
open import Category.Monad using (RawMonad)
open import Data.Product

-- This is a `Maybe`-like data type except that nothing
-- is extended with a string argument, to carry around the error.
data Err {a} (A : Set a) : Set a where
  error : String → Err A
  ok : A → Err A

-- Our representation for programs: it is either a string containing
-- textual representation of the extracted program or an error that
-- happened during extraction.
Prog = Err String

-- Simply for convenience
Strings = List String

-- We define a custom RawMonoid to add `_++/_` (list join)
-- an its overloadings.
record RawMonoid {a}(A : Set a) : Set a where
  field
    _++_ : A → A → A
    ε : A
  _++/_ : (delim : A) → List A → A
  d ++/ [] = ε
  d ++/ (x ∷ []) = x
  d ++/ (x ∷ xs) = x ++ d ++ d ++/ xs

  infixr 5 _++_

open RawMonoid {{...}} public


instance
  monoidLst : ∀ {a}{A : Set a} → RawMonoid (List A)
  monoidLst {A = A} = record {
    _++_ = Data.List._++_;
    ε = []
    }

  monoidStr : RawMonoid String
  monoidStr = record {
    _++_ = Data.String._++_;
    ε = ""
    }

  monoidErrStr : RawMonoid (Err String)
  monoidErrStr = record {
    _++_ =  λ where
      (error s) _ → error s
      _ (error s) → error s
      (ok s₁) (ok s₂) → ok (s₁ ++ s₂)
    ;
    ε = ok ""
    }

-- Simplify handling concatenation of `Prog`s and `String`s
data Err++Ty : Set → Set → Set where
  instance
    s-s : Err++Ty String String
    e-s : Err++Ty Prog String
    s-e : Err++Ty String Prog
    e-e : Err++Ty Prog Prog

infixr 5 _⊕_
_⊕_ : ∀ {A B}{{t : Err++Ty A B}} → A → B → Prog
_⊕_ {{t = s-s}} a         b = ok (a ++ b)
_⊕_ {{t = e-s}} (error x) b = error x
_⊕_ {{t = e-s}} (ok x)    b = ok (x ++ b)
_⊕_ {{t = s-e}} a (error x) = error x
_⊕_ {{t = s-e}} a    (ok x) = ok (a ++ x)
_⊕_ {{t = e-e}} a         b = a ++ b


-- The state used at the top-most and term-level compilation.
record KS : Set where
  constructor ks
  field funs : Names   -- Functions to compile
        base : Names   -- Atomic functions that we do not traverse into.
        done : Names   -- Functions that we have processed.
        cnt  : ℕ       -- Source of fresh variables

SKS = State KS
TCS = StateT KS TC

instance
  monadTC = RCat.monad

  monadTCS : RawMonad TCS
  monadTCS = StateTMonad KS monadTC

  monadSKS : ∀ {S : Set} → RawMonad (State S)
  monadSKS {S} = StateMonad S

  monadErr : ∀ {f} → RawMonad {f} Err
  monadErr = record {
    return = ok ;
    _>>=_ = λ { (error s) f → error s ; (ok a) f → f a }
    }

lift-state : ∀ {f}{M}{RM : RawMonad {f} M}{A}{S} → M A → StateT S M A
lift-state {RM = RM} x = λ s → return (_, s) ⊛ x
          where open RawMonad RM


lift-mstate : ∀ {f}{M}{RM : RawMonad {f} M}{A}{S} → State S A → StateT S M A
lift-mstate {RM = RM}{S = S} sa = λ s → return (sa s)
                          where open RawMonad RM

-- Modify error message in Prog, in case Prog is error.
err-modify : Prog → (String → String) → Prog
err-modify (error s) f = error (f s)
err-modify p _ = p
