open import Structures

open import Data.String using (String; _≈?_)
open import Data.List as L using (List; []; _∷_; [_])
open import Data.List.Categorical
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as ℕ
open import Data.Nat.DivMod
open import Agda.Builtin.Nat using (div-helper; mod-helper)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Fin as F using (Fin; zero; suc; #_)

open import Category.Monad
open import Category.Monad.State

open import Data.Product as Σ
open import Data.Unit
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin; zero; suc; fromℕ<)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary

open import Reflection hiding (return; _>>=_; _>>_)
open import Reflection.Term
import      Reflection.Name as RN
open import Function

open RawMonad ⦃ ... ⦄



Id = String

data Op : Set where
  Plus Minus Times Divide Eq Neq And Gt Lt : Op

data Expr : Set where
  Nat : ℕ → Expr
  BinOp : Op → Expr → Expr → Expr
  Var : String → Expr
  Call : Id → List Expr → Expr
  Function : Id → List Id → Expr → Expr
  Extern : Id → List Id → Expr
  Let : Id → Expr → Expr → Expr
  Assert : Expr → Expr
  If : Expr → Expr → Expr → Expr

op-to-string : Op → String
op-to-string Plus = "+"
op-to-string Minus = "-"
op-to-string Times = "*"
op-to-string Divide = "/"
op-to-string Eq = "=="
op-to-string Neq = "!="
op-to-string And = "&&"
op-to-string Gt = ">"
op-to-string Lt = "<"

indent : ℕ → String
indent n = "" ++/ L.replicate n "  "


flatten-lets : List Expr → List (Id × Expr) × List Expr

-- Lift all the assigns from the (potentially) nested let
flatten-let : Expr → List (Id × Expr) × Expr
flatten-let (Let x e e₁) = let a₁ , e = flatten-let e
                               a₂ , e₁ = flatten-let e₁
                           in (a₁ ++ [(x , e)] ++ a₂) , e₁
flatten-let e@(Nat _) = [] , e
flatten-let (BinOp x e e₁) = let a  , e = flatten-let e
                                 a₁ , e₁ = flatten-let e₁
                             in (a ++ a₁) , BinOp x e e₁
flatten-let e@(Var _) = [] , e
flatten-let (Call x es) = let as , es' = flatten-lets es
                          in as , Call x es'
flatten-let (Function x args e) = let a , e = flatten-let e
                                  in [] , (Function x args $ L.foldr (uncurry Let) e a)
flatten-let e@(Extern _ _) = [] , e
flatten-let (Assert e) = let a , e = flatten-let e in a , Assert e

flatten-let (If e e₁ e₂) = let a , e = flatten-let e
                               a₁ , e₁ = flatten-let e₁
                               a₂ , e₂ = flatten-let e₂
                               e₁' = L.foldr (uncurry Let) e₁ a₁
                               e₂' = L.foldr (uncurry Let) e₂ a₂
                           in a , (If e e₁' e₂')


flatten-lets [] = [] , []
flatten-lets (e ∷ es) = let a , e = flatten-let e
                            a₁ , es = flatten-lets es
                        in (a ++ a₁) , (e ∷ es)


{-# TERMINATING #-}
expr-to-string : ℕ → Expr → String
expr-to-string ind (Nat x) = indent ind
                          ++ showNat x
expr-to-string ind (BinOp op e e₁) = indent ind ++ "(" ++ expr-to-string 0 e ++ ") " ++ op-to-string op ++ " (" ++ expr-to-string 0 e₁ ++ ")"
expr-to-string ind (Var x) = indent ind
                          ++ x
expr-to-string ind (Call f args) = indent ind
                                ++ f ++ " (" ++ (", " ++/ L.map (expr-to-string 0) args) ++ ")"
expr-to-string ind (Function n ids e) = indent ind
                                     ++ "def " ++ n ++ "(" ++ (", " ++/ ids) ++ "):\n" ++ expr-to-string (ind + 1) e
expr-to-string ind (Extern n ids) = indent ind
                                 ++ "extern def " ++ n ++ " (" ++ (", " ++/ ids) ++ ")"

expr-to-string ind (Let x e@(If _ _ _) e₁) = indent ind
                               ++ "let " ++ x ++ " =\n"
                               ++ expr-to-string (ind + 1) e ++ "\n"
                               ++ expr-to-string ind e₁
expr-to-string ind (Let x e e₁) = indent ind
                               ++ "let " ++ x ++ " = " ++ expr-to-string 0 e ++ "\n"
                               ++ expr-to-string ind e₁
expr-to-string ind (Assert e) = indent ind
                             ++ "assert (" ++ expr-to-string 0 e ++ ")"
expr-to-string ind (If e e₁ e₂) = indent ind
                               ++ "if " ++ expr-to-string 0 e ++ ":\n"
                               ++ expr-to-string (ind + 1) e₁ ++ "\n"
                               ++ indent ind ++ "else:\n"
                               ++ expr-to-string (ind + 1) e₂ ++ "\n"


-- Glorified sigma type for variable-assertion pairs
record Assrt : Set where
  constructor mk
  field v : Id
        a : Expr

Assrts = List Assrt

-- The state used when traversing a Pi type.
record PS : Set where
  field
    cnt : ℕ           -- The source of unique variable names
    cur : Id      -- Current variable name (used to collect assertions from its type)
    ctx : Telescope -- Names in the telscopes to resolve deBruijn indices
    ret : Id      -- Variable that the function returns as a result.
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

record PatSt : Set where
  constructor mk
  field
    vars    : List (String × ℕ) --Strings
    assigns : List (Id × Expr)
    conds   : List Expr
    cnt     : ℕ

defaultPatSt : PatSt
defaultPatSt = mk [] [] [] 1


SPS = State PS


kompile-fun    : Type → Term → Name → SKS $ Err Expr
kompile-pi     : Type → SPS $ Err ⊤
{-# TERMINATING #-}
kompile-cls    : Clauses → (vars : Strings) → (ret : String) → SKS $ Err Expr
kompile-clpats : Telescope → (pats : List $ Arg Pattern) → (exprs : List Expr) → PatSt → Err PatSt
--{-# TERMINATING #-}
kompile-term   : Term → Telescope → SKS $ Err Expr

kompile-funp   : Type → Term → Name → SKS Prog
kompile-funp ty te n = do
  (ok e) ← kompile-fun ty te n where (error x) → return $ error x
  let a , e = flatten-let e
      e = case a of λ where
            [] → e
            a  → L.foldr (uncurry Let) e a
  return $ ok $ expr-to-string 0 e

private
  kf : String → Err Expr
  kf x = error $ "kompile-fun: " ++ x

  module R = RawMonadState (StateMonadState KS)


kompile-fun ty (pat-lam [] []) n =
  return $ kf "got zero clauses in a lambda term"
kompile-fun ty (pat-lam cs []) n = do
  kst ← R.get
  let (_ , ps) = kompile-pi ty $ record defaultPS{ kst = kst }
      rv = PS.ret ps
      ns = showName n
      vars = L.map proj₁ $ PS.ctx ps
      args = ok $ ", " ++/ vars
      ret-assrts = list-filter (λ where (mk v _) → v ≈? rv) $ PS.assrts ps
      arg-assrts = list-filter (dec-neg λ where (mk v _) → v ≈? rv) $ PS.assrts ps
  R.put $ PS.kst ps
  (ok b) ← kompile-cls cs vars rv where (error x) → return $ error x
  return $! ok $ Function ns vars
              $ flip (L.foldr (λ where (mk v a) → Let (v ++ "_assrt") $ Assert a)) arg-assrts
              $ Let rv b
              $ flip (L.foldr (λ where (mk v a) → Let (v ++ "_assrt") $ Assert a)) ret-assrts
              $ Var rv

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

  sps-kompile-term : Term → SPS $ Err Expr
  sps-kompile-term t = do
    ps ← P.get
    lift-ks $ kompile-term t (PS.ctx ps)


kompile-ty : Type → (pi-ok : Bool) → SPS (Err ⊤)
kompile-ty (Π[ s ∶ arg i x ] y) false = kp "higher-order functions are not supported"
kompile-ty (Π[ s ∶ ty@(arg i x) ] y) true  = do
    v ← ps-fresh "x_"
    P.modify λ k → record k { cur = v }
    (ok t) ← kompile-ty x false
      where e → return e
    P.modify λ k → record k { cur = PS.ret k  -- In case this is a return type
                            ; ctx = PS.ctx k ++ L.[(v , ty)] }
    kompile-ty y true

kompile-ty (con c args) pi-ok =
  kp $ "don't know how to handle `" ++ showName c ++ "` constructor"
kompile-ty (def (quote ℕ) args) _ = return $ ok tt
kompile-ty (def (quote Bool) args) _ = return $ ok tt

kompile-ty (def (quote _≡_) (_ ∷ arg _ ty ∷ arg _ x ∷ arg _ y ∷ [])) _ = do
  ok x ← sps-kompile-term x where error x → ke x
  ok y ← sps-kompile-term y where error x → ke x
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v (BinOp Eq x y))
  return $ ok tt

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
tel-rename ((v , ty) ∷ tel) db with list-find-el ((_≈? v) ∘ proj₁) db
... | just (_ , n) = (v ++ "_" ++ showNat n , ty)
                     ∷ tel-rename tel (list-update-fst ((_≈? v) ∘ proj₁) db (Σ.map₂ suc))
... | nothing      = (v , ty)
                     ∷ tel-rename tel ((v , 1) ∷ db)


private
  kc : String → SKS $ Err Expr
  kc x = return $ error $ "kompile-cls: " ++ x

  _>>=e_ : ∀ {a}{X : Set a} → Err X → (X → SKS $ Err Expr) → SKS $ Err Expr
  (error s) >>=e _ = return $ error s
  (ok x)    >>=e f = f x



kompile-tel : Telescope → SPS (Err ⊤)
kompile-tel [] = return $ ok tt
kompile-tel ((v , t@(arg i x)) ∷ tel) = do
  (ok τ) ← kompile-ty x false where (error x) → return $ error x
  P.modify λ k → record k{ ctx = PS.ctx k ++ [( v , t )] }
  kompile-tel tel


fold-expr : (Expr → Expr → Expr) → Expr → List Expr → Expr
fold-expr f e [] = e
fold-expr f _ (x ∷ []) = x
fold-expr f e (x ∷ xs) = f x (fold-expr f e xs)

kompile-cls [] ctx ret = kc "zero clauses found"
kompile-cls (clause tel ps t ∷ []) ctx ret =
  -- Make telscope names unique.
  let tel = (tel-rename $! tel) $! [] in
  kompile-clpats tel ps (L.map Var ctx) defaultPatSt >>=e λ pst → do
  let (mk vars assgns _ _) = pst --in
  ok t ← kompile-term t $! tel where (error x) → kc x
  let as = flip (L.foldr (uncurry Let)) assgns
  return $ ok $ as
              $ t
              --Let ret t
              --$ Var ret

kompile-cls (absurd-clause tel ps ∷ []) ctx ret =
  -- Exactly the same as above
  -- We don't really need to make this call, but we keep it
  -- for sanity checks.  I.e. if we'll get an error in the
  -- patterns, it will bubble up to the caller.
  kompile-clpats ((tel-rename $! tel) $! []) ps (L.map Var ctx) defaultPatSt >>=e λ pst → do
  return $ ok $ Assert (Nat 0)

kompile-cls (absurd-clause tel ps ∷ ts@(_ ∷ _)) ctx ret =
  kompile-clpats ((tel-rename $! tel) $! []) ps (L.map Var ctx) defaultPatSt >>=e λ pst → do
  let (mk vars _ conds _) = pst
      cs = fold-expr (BinOp And) (Nat 1) conds
  ok r ← kompile-cls ts ctx ret where (error x) → kc x
  return $ ok $ If cs (Assert (Nat 0)) r

kompile-cls (clause tel ps t ∷ ts@(_ ∷ _)) ctx ret =
  kompile-clpats ((tel-rename $! tel) $! []) ps (L.map Var ctx) defaultPatSt >>=e λ pst → do
  let (mk vars assgns conds _) = pst
      cs = fold-expr (BinOp And) (Nat 1) conds
      as = flip (L.foldr (uncurry Let)) assgns
  ok t ← kompile-term t $! tel where (error x) → kc x --telv --{!!} --PS.ctx ps
  ok r ← kompile-cls ts ctx ret where (error x) → kc x
  return $ ok $ If cs (as t) r


tel-lookup-name : Telescope → ℕ → Prog
tel-lookup-name tel n with n ℕ.<? L.length (L.reverse tel)
... | yes n<l = ok $ proj₁ $ L.lookup (L.reverse tel) $ fromℕ< n<l
... | no _ = error "Variable lookup in telescope failed"

private
  kcp : String → Err PatSt
  kcp x = error $ "kompile-clpats: " ++ x

  infixl 10 _+=c_ _+=a_ _+=v_ _+=n_
  _+=c_ : PatSt → Expr → PatSt
  p +=c c = record p { conds = PatSt.conds p ++ [ c ] }

  _+=a_ : PatSt → _ → PatSt
  p +=a a = record p { assigns = PatSt.assigns p ++ [ a ] }

  _+=v_ : PatSt → String × ℕ → PatSt
  p +=v v = record p { vars = PatSt.vars p ++ [ v ] }

  _+=n_ : PatSt → ℕ → PatSt
  p +=n n = record p { cnt = PatSt.cnt p + 1 }

  pst-fresh : PatSt → String → Err $ String × PatSt
  pst-fresh pst x =
    return $ x ++ showNat (PatSt.cnt pst) , pst +=n 1

kompile-clpats tel (arg i (con (quote true) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c v {- != 0 -} --is true
kompile-clpats tel (arg i (con (quote false) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c BinOp Eq v (Nat 0)

kompile-clpats tel (arg i (con (quote ℕ.zero) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c BinOp Eq v (Nat 0) --(v == 0)
kompile-clpats tel (arg i (con (quote ℕ.suc) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) (BinOp Minus v (Nat 1) ∷ ctx) $ pst +=c BinOp Gt v (Nat 0) --(v > 0)
-- For refl we don't need to generate a predicate, as refl is an element of a singleton type.
kompile-clpats tel (arg i (con (quote refl) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx pst

kompile-clpats tel (arg (arg-info _ r) (var i) ∷ l) (v ∷ vars) pst = do
  s ← tel-lookup-name tel i
  let pst = pst +=v (s , i)
  let pst = if does (s ≈? "_")
            then pst
            else pst +=a (s , v)
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
kompile-clpats tel ps ctx patst = kcp $ "failed on pattern: ["
                                     ++ (", " ++/ L.map (λ where (arg _ x) → showPattern x) ps)
                                     ++ "], ctx: [" ++ (", " ++/ (L.map (expr-to-string 0) ctx)) ++ "]"





private
  kt : ∀ {X} → String → SKS $ Err X
  kt x = return $ error $ "kompile-term: " ++ x


mk-mask : (n : ℕ) → List $ Fin n
mk-mask zero =    []
mk-mask (suc n) = L.reverse $ go n (suc n) ℕ.≤-refl
  where
    sa<b⇒a<b : ∀ a b → suc a ℕ.< b → a ℕ.< b
    sa<b⇒a<b zero    (suc b) _        = ℕ.s≤s ℕ.z≤n
    sa<b⇒a<b (suc a) (suc n) (ℕ.s≤s pf) = ℕ.s≤s $ sa<b⇒a<b a n pf

    go : (m n : ℕ) → m ℕ.< n → List $ Fin n
    go 0       (suc _) _  = zero ∷ []
    go (suc m) n       pf = F.fromℕ< pf ∷ go m n (sa<b⇒a<b m n pf)

le-to-el : ∀ {a}{X : Set a} → List (Err X) → Err (List X)
le-to-el [] = ok []
le-to-el (x ∷ l) = _∷_ <$> x ⊛ le-to-el l

kompile-arglist : (n : ℕ) → List $ Arg Term → List $ Fin n → Telescope → SKS $ Err (List Expr)
kompile-arglist n args mask varctx with L.length args ℕ.≟ n | V.fromList args
... | yes p | vargs rewrite p = do
                 l ← mapM (λ where (arg _ x) → kompile-term x varctx)
                          $ L.map (V.lookup vargs) mask
                 return $ le-to-el l
              where open TraversableM (StateMonad KS)

... | no ¬p | _ = kt "Incorrect argument mask"

kompile-term (var x []) vars =
  return $ Var <$> tel-lookup-name vars x

kompile-term (var x args@(_ ∷ _)) vars = do
  let f = tel-lookup-name vars x
      l = L.length args
  args ← kompile-arglist l args (mk-mask l) vars
  return $ Call <$> f ⊛ args

kompile-term (lit l@(nat x)) vars = return $ ok $ Nat x

kompile-term (con (quote ℕ.zero) _) _ =
  return $ ok $ Nat 0
kompile-term (con (quote ℕ.suc) (arg _ a ∷ [])) vars = do
  a ← kompile-term a vars
  return $ BinOp <$> ok Plus ⊛ ok (Nat 1) ⊛ a

kompile-term (con (quote refl) _) _ =
  return $ ok $ Nat 1

kompile-term (con c _) vars  = kt $ "don't know constructor " ++ (showName c)

-- From Agda.Builtin.Nat: div-helper k m n j = k + (n + m - j) div (1 + m)
kompile-term (def (quote div-helper) (arg _ k ∷ arg _ m ∷ arg _ n ∷ arg _ j ∷ [])) vars = do
  k ← kompile-term k vars
  m ← kompile-term m vars
  n ← kompile-term n vars
  j ← kompile-term j vars
  let n+m = BinOp <$> ok Plus ⊛ n ⊛ m
      n+m-j = BinOp <$> ok Minus ⊛ n+m ⊛ j
      k+[n+m-j] = BinOp <$> ok Plus ⊛ k ⊛ n+m-j
      1+m = BinOp <$> ok Plus ⊛ ok (Nat 1) ⊛ m
  return $ BinOp <$> ok Divide ⊛ k+[n+m-j] ⊛ 1+m

kompile-term (def (quote ℕ._≟_) (arg _ a ∷ arg _ b ∷ [])) vars = do
  a ← kompile-term a vars
  b ← kompile-term b vars
  return $ BinOp <$> ok Eq ⊛ a ⊛ b

-- The last pattern in the list of `def` matches
kompile-term (def n []) _ =
  kt $ "attempting to compile `" ++ showName n ++ "` as function with 0 arguments"

kompile-term (def (quote _+_) args@(arg _ a ∷ arg _ b ∷ [])) vars = do
  a ← kompile-term a vars
  b ← kompile-term b vars
  return $ BinOp <$> ok Plus ⊛ a ⊛ b

kompile-term (def n args@(_ ∷ _)) vars = do
  R.modify λ k → record k { funs = KS.funs k ++ [ n ] }
  let n = {-nnorm $-} showName n
      l = L.length args
  args ← kompile-arglist l args (mk-mask l) vars
  return $ Call <$> ok n ⊛ args

kompile-term t vctx = kt $ "failed to compile term `" ++ showTerm t ++ "`"
