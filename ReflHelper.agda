open import Reflection
open import Reflection.Term
open import Reflection.Universe
open import Reflection.Annotated
open import Agda.Builtin.Reflection using (withReconstructed; dontReduceDefs; onlyReduceDefs)
open import Relation.Nullary
open import Data.String as S
open import Data.Maybe hiding (_>>=_)
open import Data.Unit
open import Function
open import Data.List as L
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Nat
open import Data.Product
open import Data.Bool

-- Get a reference to the local term such as where-function or
-- with- or rewrite- by its name.
get-defn : String → AnnotationFun (λ _ → Maybe Name)
get-defn n ⟨term⟩ (def f x) with showName f S.≟ n
...                         | yes _ = just f
...                         | no  _ = nothing
get-defn n u t = defaultAnn nothing _<∣>_ u t

do-get-defn : String → ∀ {u} → (t : ⟦ u ⟧) → Annotated (λ _ → Maybe Name) t
do-get-defn n = annotate (get-defn n)


to-pat-lam : Definition → TC (Maybe Term)
to-pat-lam (function cs) = return $ just (pat-lam cs [])
to-pat-lam _ = return $ nothing

tel-norm : Names → Telescope → Telescope → TC Telescope
tel-norm base-funs [] ctx = return []
tel-norm base-funs ((v , arg i x) ∷ tel) ctx = do
  x ← dontReduceDefs base-funs
      $ inContext (reverse $ L.map proj₂ ctx)
      $ withReconstructed
      $ normalise x
      --$ reduce x
  let p = (v , arg i x)
  tel ← tel-norm base-funs tel (ctx L.++ [ p ])
  return $! p ∷ tel

pat-lam-norm : Term → Names → TC Term
pat-lam-norm (pat-lam cs args) base-funs = do
  cs ← hlpr cs
  return $ pat-lam cs args
  where
    hlpr : List Clause → TC $ List Clause
    hlpr [] = return []
    hlpr (clause tel ps t ∷ l) = do
      --gctx ← getContext

      -- Try normalising telescope
      tel ← tel-norm base-funs tel []
      let ctx = reverse $ L.map proj₂ tel
      t ← dontReduceDefs base-funs
          $ inContext ctx --(gctx L.++ ctx)
          $ withReconstructed
          $ normalise t
          --$ reduce t
      l ← hlpr l
      return $! clause tel ps t ∷ l
    hlpr (absurd-clause tel ps ∷ l) = do
      l ← hlpr l
      return $! absurd-clause tel ps ∷ l
pat-lam-norm t _ = return t



get-term : (f : Name) (base-funs : List Name) → TC Term
get-term t bf = do
     td ← withReconstructed $ dontReduceDefs bf $ getDefinition t
     just te ← to-pat-lam td where _ → typeError [ strErr $ "get-term: " S.++ showName t S.++ " is not a function" ]
     te ← pat-lam-norm te bf
     return te

get-ty : (f : Name) (base-funs : List Name) → TC Term
get-ty t bf = do
     ty ← getType t
     withReconstructed $ dontReduceDefs bf $ normalise ty


-- A helper function to get a term or a type (first parameter true/false) using
-- the chain of names so that we could traverse into helper functions.  For example
-- assume that `f` has  `with-x` in its body which in turn has `rewrite-y` which we
-- want to obtain.  Then we should call frefln as follows:
--
--     frefln true ("with-x" ∷ "rewrite-y" ∷ []) (base-funs) (quote f)
frefln-h : Bool → (name-chain : List String) (base-funs : Names) → Name → TC Term
frefln-h true [] bf t  = get-term t bf
frefln-h false [] bf t = get-ty t bf
frefln-h te/ty (x ∷ ns) bf t = do
     xt ← get-term t bf
     case (ann $ do-get-defn x {⟨term⟩} xt) of λ where
       (nothing) → typeError [ strErr $ "frefln: cannot find name `" S.++ x S.++ "` in term " S.++ showName t ]
       (just f') → frefln-h te/ty ns bf f'


macro
  frefl : Name → List Name → Term → TC ⊤
  frefl n bf a = frefln-h true [] bf n >>= quoteTC >>= unify a

  fty : Name → List Name → Term → TC ⊤
  fty n bf a = frefln-h false [] bf n >>= quoteTC >>= unify a

  frefln : Name → List Name → List String → Term → TC ⊤
  frefln n bf ns a = frefln-h true ns bf n >>= quoteTC >>= unify a

  ftyn : Name → List Name → List String → Term → TC ⊤
  ftyn n bf ns a = frefln-h false ns bf n >>= quoteTC >>= unify a
{-
  -- For debugging purposes.
  frefl : Name → List Name → Term → TC ⊤
  frefl f base-funs a = do

     ty ← getType f
     ty ← withReconstructed $ dontReduceDefs base-funs $ normalise ty
     te ← withReconstructed $ getDefinition f >>= λ where
           (function cs) → return $ pat-lam cs []
           _ → return unknown
     te ← pat-lam-norm te base-funs
     q ← quoteTC te
     unify a q

  fty : Name → List Name → Term → TC ⊤
  fty f base-funs a = do
     ty ← getType f
     ty ← withReconstructed $ dontReduceDefs base-funs $ normalise ty
     q ← quoteTC ty
     unify a q

  -- XXX We can generalise this to List of names, then the local function can be
  -- at arbitrary depth.
  frefl2 : Name → String → Term → TC ⊤
  frefl2 f na a = do
     td ← withReconstructed $ getDefinition f
     just te ← to-pat-lam td where _ → typeError [ strErr "ERROR₁" ]
     te ← pat-lam-norm te []
     --te ← normalise te
     case (ann $ do-get-defn na {⟨term⟩} te) of λ where
       (nothing) → typeError [ strErr "ERROR₁" ]
       (just f') → do
          td' ← withReconstructed $ getDefinition f
          just te ← to-pat-lam td' where _ → typeError [ strErr "ERROR₃" ]
          quoteTC te >>= unify a

  fty2 : Name → String → Term → TC ⊤
  fty2 f na a = do
     td ← withReconstructed $ getDefinition f
     just te ← to-pat-lam td where _ → typeError [ strErr "ERROR₁" ]
     te ← pat-lam-norm te []
     --te ← normalise te
     case (ann $ do-get-defn na {⟨term⟩} te) of λ where
       (nothing) → typeError [ strErr "ERROR₁" ]
       (just f') → do
          ty ← getType f'
          ty ← withReconstructed $ normalise ty
          quoteTC ty >>= unify a
-}
