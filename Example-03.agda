open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat as N using (ℕ; zero; suc; _≤_; _≥_; _<_; s≤s; z≤n)
import      Data.Nat.DivMod as N
open import Data.Nat.Properties as N
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
import      Data.Vec.Properties as V
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Product as Prod using (Σ; _,_; curry; uncurry) renaming (_×_ to _⊗_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import Function

open import Array.Base
open import Array.Properties

open import APL2

open import Agda.Builtin.Float

v→a : ∀ {a}{X : Set a}{n} → Vec X n → Ar X 1 (n ∷ [])
v→a s = imap (λ iv → V.lookup s $ ix-lookup iv zero )

a→v : ∀ {a}{X : Set a}{s} → Ar X 1 (s ∷ []) → Vec X s
a→v (imap x) = V.tabulate λ i → x (i ∷ [])

-- blog←{⍺×⍵×1-⍵}
blog : ∀ {n s} → Ar Float n s → Ar Float n s → Ar Float n s
blog α ω = α ×ᵣ ω ×ᵣ 1.0 -ᵣ ω

test-blog = a→v $ blog (v→a $ 3.0 ∷ 4.0 ∷ []) (v→a $ 5.0 ∷ 6.0 ∷ [])

kblog = kompile blog [] []
test₃₆ : kblog ≡ ok _
test₃₆ = refl



-- backbias←{+/,⍵}
backbias : ∀ {n s} → Ar Float n s → Scal Float
backbias ω = --(▾_ ∘₂ _+ᵣ_) / , ω
             _+ᵣ′_ / , ω
  where
    --_+ᵣ′_ : Float → Float → Float
    --a +ᵣ′ b = ▾ (a +ᵣ b)

    _+ᵣ′_ = primFloatPlus


kbackbias = kompile backbias (quote prod ∷ []) (quote prod ∷ quote off→idx ∷ quote reduce-custom.reduce-1d ∷ [])
--test₃₇ : kbackbias ≡ ok _
--test₃₇ = refl


-- logistic←{÷1+*-⍵}
logistic : ∀ {n s} → Ar Float n s → Ar Float n s
logistic ω = ÷ᵣ 1.0 +ᵣ *ᵣ -ᵣ ω

klogistic = kompile logistic [] []
test₃₈ : klogistic ≡ ok _
test₃₈ = refl

-- meansqerr←{÷∘2+/,(⍺-⍵)*2}
meansqerr : ∀ {n s} → Ar Float n s → Ar Float n s → Scal Float
meansqerr α ω = _÷ᵣ 2.0 $ _+ᵣ′_ / , (α +ᵣ ω) ×ᵣ (α -ᵣ ω)
  where
    _+ᵣ′_ = primFloatPlus

kmeansqerr = kompile meansqerr (quote prod ∷ []) (quote prod ∷ quote off→idx ∷ quote reduce-custom.reduce-1d ∷ [])
test₃₉ : klogistic ≡ ok _
test₃₉ = refl

-- backavgpool←{2⌿2/⍵÷4}⍤2
backavgpool : ∀ {s} → Ar Float 2 s → Ar Float 2 $ ▾ (2 × s)
backavgpool {s = _ ∷ _ ∷ []} ω = 2 /ᵣ′ 2 ⌿ᵣ ω ×ᵣ 4.0
  where
    infixr 20 _/ᵣ′_
    _/ᵣ′_ = _/ᵣ_ {s = _ ∷ []}

kbackavgpool = kompile backavgpool [] []
test₄₀ : kbackavgpool ≡ ok _
test₄₀ = refl



-- Something that could go in Stdlib.
≡⇒≤ : ∀ {a b} → a ≡ b → a N.≤ b
≡⇒≤ refl = ≤-refl

-- This should be perfectly generaliseable --- instead of 2
-- we can use any m>0
a<b⇒k<2⇒a*2+k<b*2 : ∀ {a b k} → a N.< b → k N.< 2 → a N.* 2 N.+ k N.< b N.* 2
a<b⇒k<2⇒a*2+k<b*2 {a} {b} {zero} a<b k<2
                  rewrite (+-identityʳ (a N.* 2))
                        | (*-comm a 2)
                        | (*-comm b 2) = *-monoʳ-< 1 a<b
a<b⇒k<2⇒a*2+k<b*2 {a} {b} {suc zero} a<b k<2 = ≤-trans (N.s≤s (≡⇒≤ (+-comm _ 1)))
                                                        (*-monoˡ-≤ 2 a<b) 
a<b⇒k<2⇒a*2+k<b*2 {a} {b} {suc (suc k)} a<b (N.s≤s (N.s≤s ()))

A<B⇒K<2⇒A*2+K<B*2 : ∀ {n s}{a b k : Ar ℕ n s} → a <a b → k <a (cst 2) → ((a × 2) + k) <a (b × 2)
A<B⇒K<2⇒A*2+K<B*2 {a = imap a} {imap b} {imap k} a<b k<2 = λ iv → a<b⇒k<2⇒a*2+k<b*2 (a<b iv) (k<2 iv)

avgpool : ∀ {s}
        → Ar Float 2 $ ▾ (s × 2)
        → Ar Float 2 s
avgpool {s} (imap p) = imap body
  where
    body : _ → _
    body iv = ▾ (_÷ᵣ 4.0 $ _+ᵣ′_ / , f ̈ ι [2,2])
      where
         [2,2] = cst {s = 2 ∷ []} 2
         f : _ → _
         f (i , pf) = let ix , ix<s = ix→a iv in
                      p $ a→ix ((ix × 2) + i) (s × 2) $ A<B⇒K<2⇒A*2+K<B*2 ix<s pf
         _+ᵣ′_ = primFloatPlus

kavgpool = kompile avgpool [] []












-- Verbose facts about transitivity of <, ≤, and ≡
a≤b⇒b≡c⇒a≤c : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
a≤b⇒b≡c⇒a≤c a≤b refl = a≤b

a≤b⇒a≡c⇒b≡d⇒c≤d : ∀ {a b c d} → a ≤ b → a ≡ c → b ≡ d → c ≤ d
a≤b⇒a≡c⇒b≡d⇒c≤d a≤b refl refl = a≤b

a<b⇒0<b : ∀ {a b} → a < b → zero < b
a<b⇒0<b {a} a<b = ≤-trans (s≤s z≤n) a<b

a<b⇒c≤a⇒c<b : ∀ {a b c} → a < b → c ≤ a → c < b
a<b⇒c≤a⇒c<b a<b z≤n = a<b⇒0<b a<b
a<b⇒c≤a⇒c<b (s≤s a<b) (s≤s c≤a) = s≤s (a<b⇒c≤a⇒c<b a<b c≤a)

a≤b⇒c≤a⇒c≤b : ∀ {a b c} → a ≤ b → c ≤ a → c ≤ b
a≤b⇒c≤a⇒c≤b {a} {b} {c} a≤b c≤a = ≤-trans c≤a a≤b

A<B⇒B≤C⇒A≤C : ∀ {n}{ix s s₁ : Ar ℕ 1 (n ∷ [])}
             → ix <a s → s₁ ≥a s → s₁ ≥a ix
A<B⇒B≤C⇒A≤C {ix = imap x} {imap x₁} {imap x₂} ix<s ix≤s₁ iv = ≤-trans (<⇒≤ $ ix<s iv) (ix≤s₁ iv)

A≥B⇒A≡C⇒C≥B : ∀ {d s}{A B C : Ar ℕ d s}
             → A ≥a B → A =a C → C ≥a B
A≥B⇒A≡C⇒C≥B {A = imap x} {imap x₁} {imap x₂} A≥B A≡C iv rewrite (sym $ A≡C iv) = A≥B iv

-- Something that could go in Stdlib.

a≤a*b : ∀ {a b} → a ≤ a N.* suc b 
a≤a*b {a} {b = zero} rewrite (*-identityʳ a) = ≤-refl
a≤a*b {a} {b = suc b} = ≤-trans a≤a*b (*-monoʳ-≤ a (≤-step ≤-refl))


a-s[b]+1≡a-b : ∀ {a b} → b < a →  a N.∸ suc b N.+ 1 ≡ a N.∸ b
a-s[b]+1≡a-b {a} {b} pf = begin
                     a N.∸ suc (b) N.+ 1  ≡⟨ sym $ N.+-∸-comm 1 pf ⟩
                     a N.+ 1 N.∸ suc b    ≡⟨ cong₂ N._∸_ (N.+-comm a 1) (refl {x = suc b}) ⟩
                     a N.∸ b
                   ∎
                   where open ≡-Reasoning

conv-ix-inb : ∀ {n}{ix s s₁ : Ar ℕ 1 (n ∷ [])}
            → (ix<s : ix <a s)
            → (s₁≥s : s₁ ≥a s)
            → (s₁ - ix) {≥ = A<B⇒B≤C⇒A≤C {s₁ = s₁} ix<s s₁≥s}
               ≥a ((s₁ - s) {≥ = s₁≥s} + ( 1))
conv-ix-inb {ix = imap ix} {imap s} {imap s₁} ix<s s₁≥s iv =
       let
         s₁-[1+ix]≥s₁-s = ∸-monoʳ-≤ (s₁ iv) (ix<s iv)
         s₁-[1+ix]+1≥s₁-s+1 = +-monoˡ-≤ 1 s₁-[1+ix]≥s₁-s
       in a≤b⇒b≡c⇒a≤c s₁-[1+ix]+1≥s₁-s+1 (a-s[b]+1≡a-b {a = s₁ iv} {b = ix iv} (≤-trans (ix<s iv) (s₁≥s iv))) 

{-
undo-sa-as : ∀ {n} {s s₁ : Vec ℕ n}{ix : Ar ℕ 1 (n ∷ [])}{≥1}
     → ((imap (λ iv → V.lookup s₁ (ix-lookup iv zero)) - ix) {≥ = ≥1})
       =a imap (λ z → V.lookup (a→s ((imap (λ iv → V.lookup s₁ (ix-lookup iv zero)) - ix) {≥ = ≥1}))
                             (ix-lookup z zero))
undo-sa-as {s₁ = s₁} {ix = (imap ix)} {≥1} iv = sym $ s→a∘a→s ((s→a s₁ - imap ix) {≥ = ≥1}) iv
-}


undo-lkptab : ∀ {n s₁}{ix : Ar ℕ 1 (n ∷ [])} (iv : Ix 1 (n ∷ [])) →
      V.lookup s₁ (ix-lookup iv zero) N.∸ sel ix iv ≡
      V.lookup (V.tabulate (λ i → V.lookup s₁ i N.∸ sel ix (i ∷ [])))
      (ix-lookup iv zero)
undo-lkptab {s₁ = s₁}{ix} (i ∷ []) = sym (V.lookup∘tabulate _ i)


-- conv ← {a←⍵ ⋄ w←⍺ ⋄ ⊃+/,w×{(1+(⍴a)-⍴w)↑⍵↓a}¨⍳⍴w}
--conv : ∀ {n s s₁}
--       → Ar Float n s
--       → Ar Float n s₁
--       → {s₁≥s : s→a s₁ ≥a s→a s}
--       → let sr = a→s $ (s→a s₁ - s→a s) {≥ = s₁≥s} + 1
--         in Ar Float n sr

conv : ∀ {n wₛ aₛ}
      → Ar Float n wₛ
      → Ar Float n aₛ
      → {≥ : ▴ aₛ ≥a ▴ wₛ}
      → Ar Float n $ ▾ ((aₛ - wₛ){≥} + 1)
conv {n = n} {wₛ = s} {aₛ = s₁} w a {s₁≥s} = let
               sr = (s₁ - s) {≥ = s₁≥s} + 1
               idxs = ι ρ w

               rots ix ix<s = let
                  ~ix≥ρa = A<B⇒B≤C⇒A≤C ix<s s₁≥s
                  ix↓a = (ix ↓ a) {pf = ~ix≥ρa}
                  ~ix-inb = conv-ix-inb {s₁ = s→a s₁} ix<s s₁≥s
                  ~ρix↓a≥sr = A≥B⇒A≡C⇒C≥B ~ix-inb (undo-lkptab {s₁ = s₁}{ix = ix})
                  in
                  (sr ↑ ix↓a) {pf = ~ρix↓a≥sr }

               r = (uncurry rots) ̈ idxs
               mul = w ̈⟨ _×ᵣ_ ⟩ (subst-ar (a→s∘s→a s) r)
               res = reduce-1d _+ᵣ_ (cst 0.0) (, mul)
              in res

kconv : Prog
kconv = kompile conv (quote _≥a_ ∷ quote reduce-1d ∷ []) [] -- (quote reduce-1d ∷ [])
