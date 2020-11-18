open import Structures

module ExtractSac where
open import Data.String as S hiding (_++_) --using (String)
open import Data.List as L hiding (_++_)  --using (List; []; _∷_; [_])
open import Data.List.Categorical
open import Data.Nat as N
open import Data.Nat.Properties as N
open import Data.Nat.Show renaming (show to showNat) -- FIXME instances?
open import Data.Product hiding (map)
open import Data.Fin using (Fin; zero; suc; fromℕ<; #_)
open import Data.Vec as V using (Vec; updateAt)
open import Data.Char renaming (_≈?_ to _c≈?_)
open import Data.Bool
open import Data.Fin as F using (Fin; zero; suc; inject₁)

open import Category.Monad
open import Category.Monad.State

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

open import Reflection hiding (return; _>>=_; _>>_)
open import Reflection.Term

open import Function

open RawMonad {{...}}

-- Glorified sigma type for variable-type pairs
record VarTy : Set where
  constructor _∈_
  field v : String
        t : String

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
kompile-pi     : Type → SPS Prog
kompile-cls    : Clauses → (vars : Strings) → (ret : String) → SKS Prog
kompile-clpats : Telescope → (pats : List $ Arg Pattern) → (vars : Strings) → PatSt → Err PatSt
{-# TERMINATING #-}
kompile-term   : Term → (varctx : Strings) → SKS Prog


-- Normalise the name of the symbols (functions, constructors, ...)
-- that we obtain from showName, i.e. remove dots, replace weird
-- symbols with ascii.
nnorm : String → Prog
nnorm s = ok
        $ replace '.' '_'
        $ replace '-' '_'
        $ s
  where
    repchar : (t f x : Char) → Char
    repchar f t x with x c≈? f
    ... | yes _ = t
    ... | no  _ = x

    replace : (from to : Char) → String → String
    replace f t s = fromList $ L.map (repchar f t) $ toList s


private
  kf : String → Prog
  kf x = error $ "kompile-fun: " ++ x

  module R = RawMonadState (StateMonadState KS)

kompile-fun ty (pat-lam [] []) n =
  return $ kf "got zero clauses in a lambda term"
kompile-fun ty (pat-lam cs []) n = do
  kst ← R.get
  let (rt , ps) = kompile-pi ty $ record defaultPS{ kst = kst }
      rv = PS.ret ps
      ns = showName n
      args = ", " ++/ L.map (λ where (v ∈ t) → t ++ " " ++ v) (PS.ctx ps)
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
  kp : String → SPS Prog
  kp x = return $ error $ "kompile-pi: " ++ x

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


kompile-ty : Type → (pi-ok : Bool) → SPS Prog
kompile-ty (Π[ s ∶ arg i x ] y) false = kp "higher-order functions are not supported"
kompile-ty (Π[ s ∶ arg i x ] y) true  = do
    v ← ps-fresh "x_"
    P.modify λ k → record k { cur = v }
    (ok t) ← kompile-ty x false
      where e → return e
    P.modify λ k → record k { cur = PS.ret k  -- In case this is a return type
                            ; ctx = PS.ctx k ++ [ v ∈ t ] }
    kompile-ty y true

kompile-ty (con c args) pi-ok =
  kp $ "don't know how to handle `" ++ showName c ++ "` constructor"
kompile-ty (def (quote ℕ) args) _ = return $ ok "int"
kompile-ty (def (quote Fin) (arg _ x ∷ [])) _ = do
  (ok p) ← sps-kompile-term x where e → return e
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v $′ "assert (" ++ v ++ " < " ++ p ++ ")")
  return $ ok "int"

kompile-ty (def (quote L.List) (_ ∷ arg _ x ∷ _)) _ = do
  el ← ps-fresh "el_"
  (v , as) ← < PS.cur , PS.assrts > <$> P.get
  -- Any constraints that the subsequent call would
  -- generate will be constraints about the elements
  -- of the list.
  P.modify λ k → record k { cur = el ; assrts = [] }
  -- TODO: we are now assuming that nested arrays are ok
  --       which is not quite true (at least not with this syntax)
  τ ← kompile-ty x false
  P.modify λ k → record k {
    cur = v;
    assrts = as ++ (L.map {B = Assrt} (λ where (mk _ a) → mk v ("foreach " ++ el ++ " in " ++ v ++ ": " ++ a)) $ PS.assrts k)
    -- No need to modify context, as we don't allow higher order functions, so it stays the same.
    }
  return $ τ ⊕ "[.]"

kompile-ty (def _ _) _ = kp "TODO₁"

kompile-ty unknown _ =
  kp "found unknown in type"
kompile-ty (meta _ _) _ =
  kp  "found meta in type"
kompile-ty (pat-lam _ _) _ =
  kp "found pattern-matching lambda in type"
kompile-ty _ _ =
  kp "ERROR"


kompile-pi x = kompile-ty x true


private
  kc : String → SKS Prog
  kc x = return $ error $ "kompile-cls: " ++ x

  _>>=e_ : ∀ {a}{X : Set a} → Err X → (X → SKS Prog) → SKS Prog
  (error s) >>=e _ = return $ error s
  (ok x)    >>=e f = f x


kompile-cls [] ctx ret = kc "zero clauses found"
kompile-cls (clause tel ps t ∷ []) ctx ret =
  kompile-clpats tel ps ctx defaultPatSt >>=e λ pst → do
  let (mk vars assgns _ _) = pst
  t ← kompile-term t vars
  let as = "\n" ++/ assgns
  return $ as ⊕ "\n"
         ⊕ ret ⊕ " = " ⊕ t ⊕ ";\n"

kompile-cls (absurd-clause tel ps ∷ cs) ctx ret = kc "TODO₂"
kompile-cls (clause tel ps t ∷ ts@(_ ∷ _)) ctx ret =
  kompile-clpats tel ps ctx defaultPatSt >>=e λ pst → do
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

kompile-clpats tel (arg _ (con c _) ∷ _) (_ ∷ _) pst =
  error $ "cannot handle patern-constructor " ++ showName c

kompile-clpats tel (arg (arg-info visible r) (var i) ∷ l) (v ∷ vars) pst = do
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

kompile-clpats _ [] [] pst = ok pst
kompile-clpats tel ps ctx patst = error "TODO₅"



private
  kt : String → SKS Prog
  kt x = return $ error $ "kompile-term: " ++ x

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

kompile-term (con (quote L.List.[]) _) _ =
  return $ ok "[]"
kompile-term (con (quote L.List._∷_) args) vars = do
  args ← kompile-arglist 4 args (# 2 ∷ # 3 ∷ []) vars
  return $ "cons (" ⊕ args ⊕ ")"


kompile-term (con c _) vars  = kt $ "don't know constructor " ++ (showName c)

-- The last pattern in the list of `def` matches
kompile-term (def n args) vars = do
  R.modify λ k → record k { funs = KS.funs k ++ [ n ]  }
  let n = nnorm $ showName n
      l = L.length args
  args ← kompile-arglist l args (mk-mask l) vars
  return $ n ⊕ " (" ⊕ args ⊕ ")"

kompile-term t vctx = kt "TODO₇"
