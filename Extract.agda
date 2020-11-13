open import Structures
open import Reflection hiding (return; _>>=_; _>>_)

module Extract (kompile-fun : Type → Term → Name → SKS Prog) where

open import Reflection.Term
import      Reflection.Name as RN
open import Agda.Builtin.Reflection using (withReconstructed; dontReduceDefs; onlyReduceDefs)

open import Data.List as L hiding (_++_)
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Bool

open import Function using (_$_; case_of_)

open import Category.Monad using (RawMonad)
open import Category.Monad.State
open RawMonad {{...}} public

open import Relation.Nullary
import      Relation.Unary as UR


-- Check if there exists an element in the list that satisfies the predicate P.
list-has-el : ∀ {a b}{A : Set a}{P : UR.Pred A b} → UR.Decidable P → List A → Bool
list-has-el P? [] = false
list-has-el P? (x ∷ xs) with P? x
... | yes _ = true
... | no  _ = list-has-el P? xs

{-# TERMINATING #-}
kompile-fold   : TCS Prog

macro
  -- Main entry point of the extractor.
  -- `n` is a starting function of the extraction
  -- `base` is the set of base functions that we never traverse into.
  -- `skip` is the list of functions that we have traversed already.
  -- The difference between the two is that `base` would be passed to
  -- `dontReduceDefs`, hence never inlined; whereas `skip` mainly avoids
  -- potential recursive extraction.
  kompile : Name → Names → Names → Term → TC ⊤
  kompile n base skip hole = do
    (p , _) ← kompile-fold $ ks [ n ] base skip 1
    q ← quoteTC p
    unify hole q

  -- FIXME: this is only for debugging purposes.
  frefl : Name → List Name → Term → TC ⊤
  frefl f base-funs a = do
     (function cs) ← withReconstructed (getDefinition f)
       where _ → quoteTC "ERROR rtest: function expected" >>= unify a
     let v = (pat-lam cs [])
     q ← quoteTC v
     unify a q


-- Traverse through the list of the functions we need to extract
-- and collect all the definitions.
module R = RawMonadState (StateTMonadState KS monadTC)
kompile-fold = do
    s@(ks fs ba done c) ← R.get
    case fs of λ where
      []       → return ε
      (f ∷ fs) → case list-has-el (f RN.≟_) done of λ where
        true → do
          R.modify λ k → record k{ funs = fs }
          kompile-fold
        false → do
          -- FIXME? We have one monad inside the other (StateT TC))
          --        and I need to do a few operations within TC.
          --        Not sure whether this is the most elegant way.
          q ← λ _ → do
              ty ← getType f
              ty ← withReconstructed $ dontReduceDefs ba $ normalise ty
              te ← withReconstructed $ getDefinition f >>= λ where
                    (function cs) → return $ pat-lam cs []
                    -- FIXME: currently we do not extract data types, which
                    --        we should fix by parametrising this module by
                    --        kompile-type argument, and calling it in the
                    --        same way as we call kompile-fun now.
                    --(data-cons d) → return $ con d []
                    _ → return unknown
              te ← pat-lam-norm te ba
              -- Compile the function and make an error more specific in
              -- case compilation fails.
              case kompile-fun ty te f $ ks fs ba (f ∷ done) c of λ where
                (error s , k) → return (error ("in function " ++ showName f ++ ": " ++ s) , k)
                p             → return p
          p ← kompile-fold
          return (q ⊕ "\n\n" ⊕ p)
  where
    -- This function normalises inside of the clauses of the
    -- function.  The main usecase is to push the rewriting
    -- rules in the body of the function prior to extraction.
    pat-lam-norm : Term → Names → TC Term
    pat-lam-norm (pat-lam cs args) base-funs = do
      cs ← hlpr cs
      return $ pat-lam cs args
      where
        hlpr : List Clause → TC $ List Clause
        hlpr [] = return []
        hlpr (clause tel ps t ∷ l) = do
          let ctx = reverse $ L.map proj₂ tel
          t ← dontReduceDefs base-funs
              $ inContext ctx
              $ withReconstructed
              $ normalise t
          l ← hlpr l
          return $ clause tel ps t ∷ l
        hlpr (absurd-clause tel ps ∷ l) = do
          l ← hlpr l
          return $ absurd-clause tel ps ∷ l
    pat-lam-norm t _ = return t
