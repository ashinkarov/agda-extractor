open import Kaleid as K using ()
open import Extract (K.kompile-funp)
open import ReflHelper

open import Data.Nat
open import Data.Nat.Properties
open import Data.List as L using (List; []; _∷_)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Reflection hiding (_≟_)

open import Structures
open import Function


test1-f : ℕ → ℕ
test1-f x = 1 + x

test₁ : kompile test1-f [] [] ≡ ok _
test₁ = refl


test2-f : ℕ → ℕ → ℕ
test2-f (suc x) (suc y) = suc $ test2-f x y
test2-f _ _ = 0

test₂ : kompile test2-f [] [] ≡ ok _
test₂ = refl


test3-f : (a b : ℕ) → a ≡ b → ℕ
test3-f a b _ = a ∸ b

test₃ : kompile test3-f [] [] ≡ ok _
test₃ = refl

test4-f : (x : ℕ) → x ≡ 0 → (y : ℕ) → x ≡ y → ℕ
test4-f x () (suc y) refl
test4-f x x=0 zero x=y = 0

test₄ : kompile test4-f [] [] ≡ ok _
test₄ = refl

-- _>_ is not (yet) supported, so no test₅ for now.
test5-f : (x y : ℕ) → x > y → ℕ
test5-f 0 0 ()
test5-f 0 x _ = x
test5-f (suc x) y _ = x + y


test6-f : (x y : ℕ) → ℕ
test6-f x y with x ≟ y
... | yes pf = 1
... | _ = 2

test₆ = kompile test6-f (quote _≟_ ∷ []) []
