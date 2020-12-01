open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat as N
import      Data.Nat.DivMod as N
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import Function

open import Array.Base

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
test₃₇ : kbackbias ≡ ok _
test₃₇ = refl


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


