open import Structures
open import Reflection hiding (return; _>>=_; _>>_)
open import Reflection.Show

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


{-# TERMINATING #-}
kompile-fold   : TCS Prog
pat-lam-norm : Term → Names → TC Term

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

  -- For debugging purposes.
  frefl : Name → List Name → Term → TC ⊤
  frefl f base-funs a = do

     ty ← getType f
     ty ← withReconstructed $ dontReduceDefs base-funs $ normalise ty
     te ← withReconstructed $ getDefinition f >>= λ where
           (function cs) → return $ pat-lam cs []
           _ → return unknown
     --te ← pat-lam-norm te base-funs
     q ← quoteTC te
     unify a q

  fty : Name → List Name → Term → TC ⊤
  fty f base-funs a = do
     ty ← getType f
     ty ← withReconstructed $ dontReduceDefs base-funs $ normalise ty
     q ← quoteTC ty
     unify a q

-- This function normalises inside of the clauses of the
-- function.  The main usecase is to push the rewriting
-- rules in the body of the function prior to extraction.
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


-- Traverse through the list of the functions we need to extract
-- and collect all the definitions.
kompile-fold = do
    s@(ks fs ba done c) ← R.get
    case fs of λ where
      []       → return ε
      (f ∷ fs) → case list-has-el (f RN.≟_) done of λ where
        true → do
          R.modify λ k → record k{ funs = fs }
          kompile-fold
        false → do
          (ty , te) ← lift-state {RM = monadTC} $ do
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
              return $ ty , te
          case te of λ where
            unknown →
              return $ error $ "kompile: attempting to compile `" ++ showName f ++ "` as function"
            _ → do
                R.put (ks fs ba (f ∷ done) c)
                -- Compile the function and make an error more specific in
                -- case compilation fails.
                q ← lift-mstate {RM = monadTC} $ kompile-fun ty te f
                let q = err-modify q λ x → "in function " ++ showName f ++ ": " ++ x
                -- Do the rest of the functions
                p ← kompile-fold
                return $ p ⊕ "\n\n" ⊕ q
  where
    module R = RawMonadState (StateTMonadState KS monadTC)

