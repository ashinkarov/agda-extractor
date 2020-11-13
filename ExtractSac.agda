open import Structures

module ExtractSac where
open import Data.String as S hiding (_++_) --using (String)
open import Data.List as L hiding (_++_)  --using (List; []; _∷_; [_])
open import Data.Nat as N
open import Data.Nat.Show renaming (show to showNat) -- FIXME instances?
open import Data.Product hiding (map)
open import Data.Fin using (Fin; zero; suc; fromℕ<; #_)
open import Data.Vec as V using (Vec; updateAt)
open import Data.Char renaming (_≈?_ to _c≈?_)

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


defaultPS : PS
defaultPS = record { cnt = 1
                   ; cur = ""
                   ; ctx = []
                   ; ret = "__ret"
                   ; assrts = []
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
kompile-cls    : Clauses → List VarTy → (ret : String) → SKS Prog
kompile-clpats : Telescope → (pats : List $ Arg Pattern) → List VarTy → PatSt → Err PatSt
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


-- FIXME?: can I make these functions local to kompile-fun?
--         I tried using anonymous module, but then it doesn't like
--         that the definition is outside the module.
private
  kf : String → Prog
  kf x = error $ "kompile-fun: " ++ x

kompile-fun ty (pat-lam [] []) n =
  return $ kf "got zero clauses in a lambda term"
kompile-fun ty (pat-lam cs []) n = do
  let (rt , ps) = kompile-pi ty defaultPS
      rv = PS.ret ps
      ns = showName n
      args = ", " ++/ L.map (λ { (v ∈ t) → t ++ " " ++ v }) (PS.ctx ps)
      -- TODO
      --cs = collect-var-cons (cons ps) []
      --args-assrts = map proj₂ $ fltr cs rv
      --ret-assrts = lkup-var-cons cs rv
  b ← kompile-cls cs (PS.ctx ps) rv
  return $ "// Function " ⊕ ns ⊕ "\n"
         ⊕ rt ⊕ "\n"
         ⊕ nnorm ns ⊕ "(" ⊕ args ⊕ ") {\n"
         -- ⊕ args-assrts
         ⊕ rt ⊕ " " ⊕ rv ⊕ ";\n"
         ⊕ b -- function body
         -- ⊕ ret-assrts
         ⊕ "return " ⊕ rv ⊕ ";\n"
         ⊕ "}\n\n"

kompile-fun _ _ _ =
  return $ kf "expected pattern-matching lambda"


private
  kp : String → Prog
  kp x = error $ "kompile-pi: " ++ x

module P = RawMonadState (StateMonadState PS)
kompile-pi (Π[ s ∶ arg i x ] y) = case x of λ where
  (pi _ _) → return $ kp "higher-order functions are not supported"
  _ → do
    ps@record{cnt = c} ← P.get
    let v = "x_" ++ showNat c
    P.put $ record ps { cnt = c + 1; cur = v }
    (ok t) ← kompile-pi x
      where e → return e
    P.modify λ k → record k { cur = PS.ret k  -- In case this is a return type
                            ; ctx = PS.ctx k ++ [ v ∈ t ] }
    kompile-pi y

kompile-pi (con c args) =
  return $ kp $ "don't know how to handle `" ++ showName c ++ "` constructor"
kompile-pi (def f args) with f
...                   | quote ℕ = return $ ok "int"
...                   | _ = return $ kp "TODO₁"
kompile-pi unknown =
  return $ kp "found unknown in type"
kompile-pi (meta _ _) =
  return $ kp  "found meta in type"
kompile-pi (pat-lam _ _) =
  return $ kp "found pattern-matching lambda in type"
kompile-pi _ =
  return $ kp "ERROR"

private
  kc : String → Prog
  kc x = error $ "kompile-cls: " ++ x

kompile-cls [] ctx ret = return $ kc "zero clauses found"
kompile-cls (clause tel ps t ∷ []) ctx ret =
--   return $ "vars: " ⊕ (", " ++/ L.map (λ where (v ∈ t) → v ++ " : " ++ t) ctx)

  -- FIXME? we'd have to repeat this pattern for ecah of the 4 cases:
  -- {absurd, normal} × {1-clause, many-clauses}.  Is there a better way?
  -- `kompile-clpats` returns Err PatSt, but we are in SKS (Err String) monad...
  case kompile-clpats tel ps ctx defaultPatSt of λ where
    (error s) → return (error s)
    (ok (mk vars assgns conds _)) → do
      t ← kompile-term t vars
      let as = "\n" ++/ assgns
      return $ as ⊕ "\n"
             ⊕ ret ⊕ " = " ⊕ t ⊕ ";\n"

kompile-cls (absurd-clause tel ps ∷ cs) ctx ret = return $ error "TODO₂"
kompile-cls (clause tel ps t ∷ xs@(_ ∷ _)) ctx ret = return $ error "TODO₃"




tel-lookup-name : Telescope → ℕ → Prog
tel-lookup-name tel n with n N.<? L.length (reverse tel)
... | yes n<l = ok $ proj₁ $ lookup (reverse tel) $ fromℕ< n<l
... | no _ = error "Variable lookup in telescope failed"

-- FIXME? Not sure where it is best to define such functions.  In record?
--        but then I'd have to open a record per file...
_+=c_ : PatSt → String → PatSt
p +=c c = record p { conds = PatSt.conds p ++ [ c ] }

_+=a_ : PatSt → String → PatSt
p +=a a = record p { assigns = PatSt.assigns p ++ [ a ] }

_+=v_ : PatSt → String → PatSt
p +=v v = record p { vars = PatSt.vars p ++ [ v ] }

_+=n_ : PatSt → ℕ → PatSt
p +=n n = record p { cnt = PatSt.cnt p + 1 }

kompile-clpats tel (arg i (con c ps) ∷ l) (v ∈ _ ∷ ctx) pst
               with c
...            | quote N.zero = kompile-clpats tel l ctx $ pst +=c (v ++ " == 0")
...            | _ = error "TODO₄"

kompile-clpats tel (arg (arg-info visible r) (var i) ∷ l) (v ∈ _ ∷ vars) pst = do
           s ← tel-lookup-name tel i
           -- FIXME? this code results in a meta when calling
           --        `kompile bar [] []`.  Weird...
           let pst' = case s ≈? "_" of λ where
                        (no _) → pst +=a (s ++ " = " ++ v ++ ";")
                        _ → pst
           --let pst' = pst +=a (s ++ " = " ++ v ++ ";")
           kompile-clpats tel l vars $ pst' +=v s
kompile-clpats _ [] [] pst = ok pst
kompile-clpats tel ps ctx patst = error "TODO₅"



private
  kt : String → Prog
  kt x = error $ "kompile-term: " ++ x

var-lookup : Strings → ℕ → Prog
var-lookup []       _       = kt "Variable lookup failed"
var-lookup (x ∷ xs) zero    = ok x
var-lookup (x ∷ xs) (suc n) = var-lookup xs n

kompile-arglist : (n : ℕ) → List $ Arg Term → List $ Fin n → List String → SKS Prog
kompile-arglist n args mask varctx with L.length args N.≟ n | V.fromList args
... | yes p | vargs rewrite p = do
                 l ← mapK $ L.map (V.lookup vargs) mask
                 return $ ok ", " ++/ l
              where
                -- FIXME? This is specialised mapM, is it defined somewhere
                --        generically?
                mapK : List $ Arg Term → SKS (List Prog)
                mapK [] = return []
                mapK (arg i x ∷ xs) = do
                     x' ← kompile-term x varctx
                     xs' ← mapK xs
                     return $ x' ∷ xs'
... | no ¬p | _ = return $ kt "Incorrect argument mask"

kompile-term (var x []) vars = return $ var-lookup (reverse vars) x
kompile-term (lit l) vars = return $ ok $ showLiteral l
kompile-term (con c args) vars with c
...                            | quote N.suc = do args ← kompile-arglist 1 args [ # 0 ] vars
                                                  return $ "(1 + " ⊕ args ⊕ ")"
...                            | _ = return $ kt "TODO₆"
kompile-term t vctx = return $ kt "TODO₇"
