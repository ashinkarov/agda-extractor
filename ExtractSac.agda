open import Structures
open import SacTy

module ExtractSac where
open import Data.String as S hiding (_++_) renaming (_≟_ to _≟s_)
open import Data.List as L hiding (_++_)
open import Data.List.Categorical
open import Data.Nat as N
open import Data.Nat.Properties as N
open import Data.Nat.Show renaming (show to showNat)
open import Data.Product as Σ hiding (map)
open import Data.Sum hiding (map)
open import Data.Fin using (Fin; zero; suc; fromℕ<; #_)
open import Data.Vec as V using (Vec; [] ; _∷_)
open import Data.Char renaming (_≈?_ to _c≈?_)
open import Data.Bool
open import Data.Fin as F using (Fin; zero; suc; inject₁)
open import Data.Maybe using (Maybe; just; nothing)

open import Category.Monad
open import Category.Monad.State

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

open import Reflection hiding (return; _>>=_; _>>_)
open import Reflection.Term

open import Function

open import Array.Base
open import Array.Properties

open RawMonad ⦃ ... ⦄


-- Glorified sigma type for variable-type pairs
record VarTy : Set where
  constructor _∈_
  field v : String
        t : Err SacTy

-- Glorified sigma type for variable-assertion pairs
record Assrt : Set where
  constructor mk
  field v : String
        a : String

Assrts = List Assrt

-- The state used when traversing a Pi type.
record PS : Set where
  field
    cnt : ℕ           -- The source of unique variable names
    cur : String      -- Current variable name (used to collect assertions from its type)
    ctx : List VarTy  -- Names in the telscopes to resolve deBruijn indices
    ret : String      -- Variable that the function returns as a result.
                      -- We assume that there is always a single variable and its name
                      -- is known upfront.  We need this to generate assertions from the
                      -- return type.
    assrts : Assrts   -- Assertions that we generate per each variable.
    kst : KS          -- Compilation state (in case we have to extract some functions used in types)


defaultPS : PS
defaultPS = record { cnt = 1
                   ; cur = ""
                   ; ctx = []
                   ; ret = "__ret"
                   ; assrts = []
                   ; kst = defaultKS
                   }

-- Pack the information about new variables generated
-- by patterns in the clause, assignments to these,
-- and the list of conditions for "getting into" the
-- clause.  E.g.
--   foo : List ℕ → ℕ
--   foo (x ∷ xs) 2 = ...
--
-- Assume that we named top-level arguments [a, b]
-- Then, new variables for this clause are going to be
--     [x, xs]
-- Assignments are:
--     [x = hd a, xs = tl a]
-- Conditions are:
--     [is-cons a, b == 2]
--
-- `cnt` is merely a source of fresh variables.
record PatSt : Set where
  constructor mk
  field
    vars    : Strings
    assigns : Strings
    conds   : Strings
    cnt     : ℕ

defaultPatSt : PatSt
defaultPatSt = mk [] [] [] 1

SPS = State PS

-- The main function kit to extract sac functions.
kompile-fun    : Type → Term → Name → SKS Prog
kompile-pi     : Type → SPS (Err SacTy) --Prog
kompile-cls    : Clauses → (vars : Strings) → (ret : String) → SKS Prog
kompile-clpats : Telescope → (pats : List $ Arg Pattern) → (vars : Strings) → PatSt → Err PatSt
{-# TERMINATING #-}
kompile-term   : Term → (varctx : Strings) → SKS Prog


-- Normalise the name of the symbols (functions, constructors, ...)
-- that we obtain from showName, i.e. remove dots, replace weird
-- symbols with ascii.
nnorm : String → Prog
nnorm s = ok
        $ replace '.' "_"
        $ replace '-' "_"
        $ replace '+' "plus"
        $ s
  where
    repchar : (from : Char) (to : String) (x : Char) → String
    repchar from to x with does $ x c≈? from
    ... | true  = to
    ... | false = fromList (x ∷ [])

    replace : (from : Char) (to : String) → String → String
    replace f t s = "" ++/ L.map (repchar f t) (toList s)


private
  kf : String → Prog
  kf x = error $ "kompile-fun: " ++ x

  validate-ty : Err SacTy → Prog
  validate-ty (error x) = error x
  validate-ty (ok τ) = let τ′ = sacty-normalise τ in
                       case nested? τ′ of λ where
                         hom → ok $ sacty-to-string τ′
                         nes → error $ "sac does not support nested types, but `"
                                    ++ sacty-to-string τ′ ++ "` found"

  module R = RawMonadState (StateMonadState KS)

kompile-fun ty (pat-lam [] []) n =
  return $ kf "got zero clauses in a lambda term"
kompile-fun ty (pat-lam cs []) n = do
  kst ← R.get
  let (rt , ps) = kompile-pi ty $ record defaultPS{ kst = kst }
      rt = validate-ty rt
      rv = PS.ret ps
      ns = showName n
      args = ok ", " ++/ L.map (λ where (v ∈ t) → validate-ty t ⊕ " " ⊕ v) (PS.ctx ps)
      ret-assrts = list-filter (λ where (mk v _) → v ≈? rv) $ PS.assrts ps
      arg-assrts = list-filter (dec-neg λ where (mk v _) → v ≈? rv) $ PS.assrts ps
      assrt-to-code = ("/* " ++_) ∘ (_++ " */") ∘ Assrt.a
  R.put $ PS.kst ps
  b ← kompile-cls cs (L.map (λ where (v ∈ _) → v) $ PS.ctx ps) rv
  return $ "// Function " ⊕ ns ⊕ "\n"
         ⊕ rt ⊕ "\n" 
         ⊕ nnorm ns ⊕ "(" ⊕ args ⊕ ") {\n"
         ⊕ "\n" ++/ L.map assrt-to-code arg-assrts
         ⊕ rt ⊕ " " ⊕ rv ⊕ ";\n"
         ⊕ b -- function body
         ⊕ "\n" ++/ L.map assrt-to-code ret-assrts
         ⊕ "return " ⊕ rv ⊕ ";\n"
         ⊕ "}\n\n"

kompile-fun _ _ _ =
  return $ kf "expected pattern-matching lambda"


private
  kp : ∀ {X} → String → SPS (Err X)
  kp x = return $ error $ "kompile-pi: " ++ x

  ke : ∀ {X} → String → SPS (Err X)
  ke x = return $ error x

  module P = RawMonadState (StateMonadState PS)

  infixl 10 _p+=c_ _p+=a_
  _p+=c_ : PS → ℕ → PS
  ps p+=c n = record ps{ cnt = PS.cnt ps + n }

  _p+=a_ : PS → Assrt → PS
  ps p+=a a = record ps{ assrts = a ∷ PS.assrts ps }

  ps-fresh : String → SPS String
  ps-fresh x = do
    ps ← P.get
    P.modify (_p+=c 1)
    return $ x ++ showNat (PS.cnt ps)

  lift-ks : ∀ {X} → SKS X → SPS X
  lift-ks xf sps = let (x , sks) = xf (PS.kst sps) in x , record sps {kst = sks}

  sps-kompile-term : Term → SPS Prog
  sps-kompile-term t = do
    ps ← P.get
    lift-ks $ kompile-term t (L.map (λ where (v ∈ _) → v) $ PS.ctx ps)


kompile-ty : Type → (pi-ok : Bool) → SPS (Err SacTy)
kompile-ty (Π[ s ∶ arg i x ] y) false = kp "higher-order functions are not supported"
kompile-ty (Π[ s ∶ arg i x ] y) true  = do
    v ← ps-fresh "x_"
    P.modify λ k → record k { cur = v }
    (ok t) ← kompile-ty x false
      where e → return e
    P.modify λ k → record k { cur = PS.ret k  -- In case this is a return type
                            ; ctx = PS.ctx k ++ [ v ∈ ok t ] }
    kompile-ty y true

kompile-ty (con c args) pi-ok =
  kp $ "don't know how to handle `" ++ showName c ++ "` constructor"
kompile-ty (def (quote ℕ) args) _ = return $ ok int
kompile-ty (def (quote Bool) args) _ = return $ ok bool
kompile-ty (def (quote Fin) (arg _ x ∷ [])) _ = do
  ok p ← sps-kompile-term x where error x → ke x
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v $′ "assert (" ++ v ++ " < " ++ p ++ ")")
  return $ ok int

kompile-ty (def (quote L.List) (_ ∷ arg _ ty ∷ _)) _ = do
  el ← ps-fresh "el_"
  v , as ← < PS.cur , PS.assrts > <$> P.get
  -- Any constraints that the subsequent call would
  -- generate will be constraints about the elements
  -- of the list.
  P.modify λ k → record k { cur = el ; assrts = [] }
  ok τ ← kompile-ty ty false where e → return e
  P.modify λ k → record k {
    cur = v;
    assrts = as ++ (L.map {B = Assrt} (λ where (mk _ a) → mk v ("foreach-v " ++ el ++ " in " ++ v ++ ": " ++ a)) $ PS.assrts k)
    -- No need to modify context, as we don't allow higher order functions, so it stays the same.
    }
  return $ ok $ akd nes τ (error "lists do not have static shape") 1

kompile-ty (def (quote V.Vec) (_ ∷ arg _ ty ∷ arg _ n ∷ [])) _ = do
  el ← ps-fresh "el_"
  v , as ← < PS.cur , PS.assrts > <$> P.get
  ok p ← sps-kompile-term n where error x → ke x
  P.modify λ k → record k { cur = el ; assrts = [] }
  ok τ ← kompile-ty ty false where e → return e
  P.modify λ k → record k {
    cur = v;
    assrts = as ++ (L.map {B = Assrt} (λ where (mk _ a) → mk v ("foreach-v " ++ el ++ " in " ++ v ++ ": " ++ a)) $ PS.assrts k)
                ++ [ mk v $′ "assert (shape (" ++ v ++ ")[[0]] == " ++ p ++ ")" ]
    }
  let sh = "[" ⊕ p ⊕ "]"
  case n of λ where
    -- XXX can we possibly miss on any constant expressions?
    (lit (nat n′)) → return $ ok $ aks hom τ sh 1 V.[ n′ ]
    _              → return $ ok $ akd hom τ sh 1


kompile-ty (def (quote Ar) (_ ∷ arg _ el-ty ∷ arg _ dim ∷ arg _ sh ∷ [])) _ = do
  el ← ps-fresh "el_"
  v , as ← < PS.cur , PS.assrts > <$> P.get
  ok d ← sps-kompile-term dim where error x → ke x
  ok s ← sps-kompile-term sh where error x → ke x
  P.modify λ k → record k { cur = el ; assrts = [] }
  ok τ ← kompile-ty el-ty false where e → return e
  P.modify λ k → record k {
    cur = v;
    assrts = as ++ (L.map {B = Assrt} (λ where (mk _ a) → mk v ("foreach-a sh=" ++ s ++ " " ++ el ++ " in " ++ v ++ ": " ++ a)) $ PS.assrts k)
                ++ [ mk v $′ "assert (take (" ++ d ++ ", shape (" ++ v ++ ")) == " ++ s ++ ")" ]
                -- XXX do we want to assert stuff about rank?
    }
  case dim of λ where
    -- XXX can we possibly miss on any constant expressions?
                     -- FIXME consider AKS case here!
    (lit (nat d′)) → return $ ok $ akd hom τ (ok s) d′
    _ → return $ ok $ aud hom τ (ok s)

kompile-ty (def (quote _≡_) (_ ∷ arg _ ty ∷ arg _ x ∷ arg _ y ∷ [])) _ = do
  ok x ← sps-kompile-term x where error x → ke x
  ok y ← sps-kompile-term y where error x → ke x
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v $′ "assert (" ++ x ++ " == " ++ y ++ ")")
  return $ ok unit

kompile-ty (def n _) _ = kp $ "cannot handle `" ++ showName n ++ "` type"

kompile-ty t _ =
  kp $ "failed with the term `" ++ showTerm t ++ "`"


kompile-pi x = kompile-ty x true




-- The names in the telescopes very oftern are not unique, which
-- would be pretty disasterous if the code generation relies on them.
-- see https://github.com/agda/agda/issues/5048 for more details.
--
-- This function simply ensures that variable names are unique in
-- in the telescope.
tel-rename : Telescope → (db : List (String × ℕ)) → Telescope
tel-rename [] db = []
tel-rename ((v , ty) ∷ tel) db with list-find-el ((_≟s v) ∘ proj₁) db
... | just (_ , n) = (v ++ "_" ++ showNat n , ty)
                     ∷ tel-rename tel (list-update-fst ((_≟s v) ∘ proj₁) db (Σ.map₂ suc))
... | nothing      = (v , ty)
                     ∷ tel-rename tel ((v , 1) ∷ db)


private
  kc : String → SKS Prog
  kc x = return $ error $ "kompile-cls: " ++ x

  _>>=e_ : ∀ {a}{X : Set a} → Err X → (X → SKS Prog) → SKS Prog
  (error s) >>=e _ = return $ error s
  (ok x)    >>=e f = f x


kompile-cls [] ctx ret = kc "zero clauses found"
kompile-cls (clause tel ps t ∷ []) ctx ret =
  kompile-clpats (tel-rename tel []) ps ctx defaultPatSt >>=e λ pst → do
  let (mk vars assgns _ _) = pst
  t ← kompile-term t vars
  let as = "\n" ++/ assgns
  return $ as ⊕ "\n"
         ⊕ ret ⊕ " = " ⊕ t ⊕ ";\n"

kompile-cls (absurd-clause tel ps ∷ []) ctx ret =
  -- Exactly the same as above
  -- We don't really need to make this call, but we keep it
  -- for sanity checks.  I.e. if we'll get an error in the
  -- patterns, it will bubble up to the caller.
  kompile-clpats (tel-rename tel []) ps ctx defaultPatSt >>=e λ pst → do
  return $ ok "unreachable ();"

kompile-cls (absurd-clause tel ps ∷ ts@(_ ∷ _)) ctx ret =
  kompile-clpats (tel-rename tel []) ps ctx defaultPatSt >>=e λ pst → do
  let (mk vars _ conds _) = pst
      cs = " && " ++/ (if L.length conds N.≡ᵇ 0 then [ "true" ] else conds)
  r ← kompile-cls ts ctx ret
  return $ "if (" ⊕ cs ⊕ ") {\n"
         ⊕ "unreachable();\n"
         ⊕ "} else {\n"
         ⊕ r ⊕ "\n"
         ⊕ "}\n"

kompile-cls (clause tel ps t ∷ ts@(_ ∷ _)) ctx ret =
  kompile-clpats (tel-rename tel []) ps ctx defaultPatSt >>=e λ pst → do
  let (mk vars assgns conds _) = pst
      cs = " && " ++/ (if L.length conds N.≡ᵇ 0 then [ "true" ] else conds)
      as = "\n" ++/ assgns
  t ← kompile-term t vars
  r ← kompile-cls ts ctx ret
  return $ "if (" ⊕ cs ⊕ ") {\n"
         ⊕ as ⊕ "\n"
         ⊕ ret ⊕ " = " ⊕ t ⊕ ";\n"
         ⊕ "} else {\n"
         ⊕ r ⊕ "\n"
         ⊕ "}\n"



tel-lookup-name : Telescope → ℕ → Prog
tel-lookup-name tel n with n N.<? L.length (reverse tel)
... | yes n<l = ok $ proj₁ $ lookup (reverse tel) $ fromℕ< n<l
... | no _ = error "Variable lookup in telescope failed"

private
  infixl 10 _+=c_ _+=a_ _+=v_ _+=n_
  _+=c_ : PatSt → String → PatSt
  p +=c c = record p { conds = PatSt.conds p ++ [ c ] }

  _+=a_ : PatSt → String → PatSt
  p +=a a = record p { assigns = PatSt.assigns p ++ [ a ] }

  _+=v_ : PatSt → String → PatSt
  p +=v v = record p { vars = PatSt.vars p ++ [ v ] }

  _+=n_ : PatSt → ℕ → PatSt
  p +=n n = record p { cnt = PatSt.cnt p + 1 }

  pst-fresh : PatSt → String → Err $ String × PatSt
  pst-fresh pst x =
    return $ x ++ showNat (PatSt.cnt pst) , pst +=n 1

kompile-clpats tel (arg i (con (quote true) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c (v {- == true -})
kompile-clpats tel (arg i (con (quote false) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c ("!" ++ v)

kompile-clpats tel (arg i (con (quote N.zero) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c (v ++ " == 0")
kompile-clpats tel (arg i (con (quote N.suc) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) ((v ++ " - 1") ∷ ctx) $ pst +=c (v ++ " > 0")

kompile-clpats tel (arg i (con (quote F.zero) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c (v ++ " == 0")
kompile-clpats tel (arg i (con (quote F.suc) ps@(_ ∷ _ ∷ [])) ∷ l) (v ∷ ctx) pst = do
  (ub , pst) ← pst-fresh pst "ub_"
  -- XXX here we are not using `ub` in conds.  For two reasons:
  -- 1) as we have assertions, we should check the upper bound on function entry
  -- 2) typically, the value of this argument would be Pat.dot, which we ignore
  --    right now.  It is possible to capture the value of the dot-patterns, as
  --    they carry the value when reconstructed.
  kompile-clpats tel (ps ++ l) (ub ∷ (v ++ " - 1") ∷ ctx) $ pst +=c (v ++ " > 0")

kompile-clpats tel (arg i (con (quote L.List.[]) []) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c ("emptyvec_p (" ++ v ++ ")")
kompile-clpats tel (arg i (con (quote L.List._∷_) ps@(_ ∷ _ ∷ [])) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) (("hd (" ++ v ++ ")") ∷ ("tl (" ++ v ++ ")") ∷ ctx)
                 $ pst +=c ("nonemptyvec_p (" ++ v ++ ")")

-- Almost the same as List (extra parameter in cons)
kompile-clpats tel (arg i (con (quote V.Vec.[]) []) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c ("emptyvec_p (" ++ v ++ ")")
kompile-clpats tel (arg i (con (quote V.Vec._∷_) ps@(_ ∷ _ ∷ _ ∷ [])) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) (("len (" ++ v ++ ") - 1") ∷ ("hd (" ++ v ++ ")") ∷ ("tl (" ++ v ++ ")") ∷ ctx)
                 $ pst +=c ("nonemptyvec_p (" ++ v ++ ")")

kompile-clpats tel (arg i (con (quote refl) ps) ∷ l) (v ∷ ctx) pst =
  -- No constraints, as there could only be a single value.
  kompile-clpats tel l ctx pst

kompile-clpats tel (arg _ (con c _) ∷ _) (_ ∷ _) pst =
  error $ "cannot handle patern-constructor " ++ showName c

kompile-clpats tel (arg (arg-info _ r) (var i) ∷ l) (v ∷ vars) pst = do
  -- Note that we do not distinguish between hidden and visible variables
  s ← tel-lookup-name tel i
  let pst = pst +=v s
  let pst = if does (s ≈? "_")
            then pst
            else pst +=a (s ++ " = " ++ v ++ ";")
  {-
  -- XXX If I replace the above if with this one, I end up with
  -- the unsolved meta in the test₂ in Example.agda.  Is this a bug?
  let pst = case (s ≈? "_") of λ where
             (yes _) → pst
             (no _)  → pst +=a (s ++ " = " ++ v ++ ";")
  -}
  kompile-clpats tel l vars pst

kompile-clpats tel (arg i (dot t) ∷ l) (v ∷ vars) pst =
  -- For now we just skip dot patterns.
  kompile-clpats tel l vars pst

kompile-clpats tel (arg i (absurd _) ∷ l) (v ∷ ctx) pst =
  -- If have met the absurd pattern, we are done, as
  -- we have accumulated enough conditions to derive
  -- impossibility.  So we are simply done.
  ok pst


kompile-clpats _ [] [] pst = ok pst
kompile-clpats tel ps ctx patst = error $ "kompile-clpats failed, pattern: ["
                                       ++ (", " ++/ L.map (λ where (arg _ x) → showPattern x) ps)
                                       ++ "], ctx: [" ++ (", " ++/ ctx) ++ "]"



private
  kt : String → SKS Prog
  kt x = return $ error $ "kompile-term: " ++ x

  kt-fresh : String → SKS String
  kt-fresh x = do
    ps ← R.get
    R.modify λ k → record k{ cnt = 1 + KS.cnt k }
    return $ x ++ showNat (KS.cnt ps)

var-lookup : Strings → ℕ → SKS Prog
var-lookup []       _       = kt "Variable lookup failed"
var-lookup (x ∷ xs) zero    = return $ ok x
var-lookup (x ∷ xs) (suc n) = var-lookup xs n


mk-mask : (n : ℕ) → List $ Fin n
mk-mask zero =    []
mk-mask (suc n) = L.reverse $ go n (suc n) N.≤-refl
  where
    sa<b⇒a<b : ∀ a b → suc a N.< b → a N.< b
    sa<b⇒a<b zero    (suc b) _        = s≤s z≤n
    sa<b⇒a<b (suc a) (suc n) (s≤s pf) = s≤s $ sa<b⇒a<b a n pf

    go : (m n : ℕ) → m N.< n → List $ Fin n
    go 0       (suc _) _  = zero ∷ []
    go (suc m) n       pf = F.fromℕ< pf ∷ go m n (sa<b⇒a<b m n pf)

private
  module mask-tests where
    test-mk-mask₁ : mk-mask 0 ≡ []
    test-mk-mask₁ = refl

    test-mk-mask₂ : mk-mask 1 ≡ # 0 ∷ []
    test-mk-mask₂ = refl

    test-mk-mask₃ : mk-mask 2 ≡ # 0 ∷ # 1 ∷ []
    test-mk-mask₃ = refl

kompile-arglist : (n : ℕ) → List $ Arg Term → List $ Fin n → List String → SKS Prog
kompile-arglist n args mask varctx with L.length args N.≟ n | V.fromList args
... | yes p | vargs rewrite p = do
                 l ← mapM (λ where (arg _ x) → kompile-term x varctx)
                          $ L.map (V.lookup vargs) mask
                 return $ ok ", " ++/ l
              where open TraversableM (StateMonad KS)

... | no ¬p | _ = kt "Incorrect argument mask"

kompile-term (var x []) vars = var-lookup (reverse vars) x
kompile-term (lit l) vars = return $ ok $ showLiteral l

kompile-term (con (quote N.zero) _) _ =
  return $ ok "0"
kompile-term (con (quote N.suc) args) vars = do
  args ← kompile-arglist 1 args [ # 0 ] vars
  return $ "(1 + " ⊕ args ⊕ ")"

kompile-term (con (quote Fin.zero) _) _ =
  return $ ok "0"
kompile-term (con (quote Fin.suc) args) vars = do
  args ← kompile-arglist 2 args [ # 1 ] vars
  return $ "(1 + " ⊕ args ⊕ ")"

kompile-term (con (quote L.List.[]) (_ ∷ (arg _ ty) ∷ [])) vars = do
  -- We want to call kompile-ty, and we need a context that "should"
  -- contain vars with their types.  But, we never actually access these
  -- types in the context, we only refer to variables, therefore the
  -- following hack is justified.
  kst ← R.get
  let ctx = L.map (λ v → v ∈ error "?") vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
  --R.put (PS.kst ps)
  return $ "empty (" ⊕ in-sh ⊕ ")" --ok "[]"

kompile-term (con (quote L.List._∷_) args) vars = do
  args ← kompile-arglist 4 args (# 2 ∷ # 3 ∷ []) vars
  return $ "cons (" ⊕ args ⊕ ")"

-- Almost the same as List
kompile-term (con (quote V.Vec.[]) (_ ∷ (arg _ ty) ∷ [])) vars = do
  kst ← R.get
  let ctx = L.map (λ v → v ∈ error "?") vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
  --R.put (PS.kst ps)
  return $ "empty (" ⊕ in-sh ⊕ ")" --ok "[]"

kompile-term (con (quote V.Vec._∷_) args) vars = do
  args ← kompile-arglist 5 args (# 3 ∷ # 4 ∷ []) vars
  return $ "cons (" ⊕ args ⊕ ")"

kompile-term (con (quote refl) _) _ =
  return $ ok "tt"


-- Imaps with explicit lambdas
kompile-term (con (quote Array.Base.imap) (_ ∷ arg _ ty ∷ _ ∷ arg _ s ∷ arg _ (vLam x e) ∷ [])) vars = do
  kst ← R.get
  let ctx = L.map (λ v → v ∈ error "?") vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
  --R.put (PS.kst ps)
  iv ← kt-fresh "iv_"
  s ← kompile-term s vars
  b ← kompile-term e $ vars ++ [ iv ]
  return $ "with { (. <= " ⊕ iv ⊕ " <= .): " ⊕ b ⊕ "; }: genarray (" ⊕ s ⊕ ", zero (" ⊕ in-sh ⊕ "))"

-- Imaps with an expression
kompile-term (con (quote Array.Base.imap) (_ ∷ arg _ ty ∷ _ ∷ arg _ s ∷ arg _ e ∷ [])) vars = do
  kst ← R.get
  let ctx = L.map (λ v → v ∈ error "?") vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
  --R.put (PS.kst ps)
  iv ← kt-fresh "iv_"
  s ← kompile-term s vars
  b ← kompile-term e $ vars
  return $ "with { (. <= " ⊕ iv ⊕ " <= .): " ⊕ b ⊕ " (" ⊕ iv ⊕ "); }: genarray (" ⊕ s ⊕ ", zero (" ⊕ in-sh ⊕ "))"


kompile-term (con c _) vars  = kt $ "don't know constructor " ++ (showName c)


kompile-term (def (quote N._+_) args) vars =
  ("_add_SxS_ (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 2 args (mk-mask 2) vars
kompile-term (def (quote N._*_) args) vars =
  ("_mul_SxS_ (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 2 args (mk-mask 2) vars

-- Array stuff
kompile-term (def (quote sel) (_ ∷ _ ∷ _ ∷ _ ∷ arg _ a ∷ arg _ iv ∷ [])) vars = do
  a ← kompile-term a vars
  iv ← kompile-term iv vars
  return $ a ⊕ "[" ⊕ iv ⊕ "]"

-- The last pattern in the list of `def` matches
kompile-term (def n []) _ =
  kt $ "attempting to compile `" ++ showName n ++ "` as function with 0 arguments"

kompile-term (def n args@(_ ∷ _)) vars = do
  R.modify λ k → record k { funs = KS.funs k ++ [ n ] }
  let n = nnorm $ showName n
      l = L.length args
  args ← kompile-arglist l args (mk-mask l) vars
  return $ n ⊕ " (" ⊕ args ⊕ ")"

kompile-term t vctx = kt $ "failed to compile term `" ++ showTerm t ++ "`"
