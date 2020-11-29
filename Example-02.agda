open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import Function

open import Array.Base

-- Check that Vec² and List ∘ Vec are treated correctly.
-- Here we transpose a 2d array using Vec operations.
-- Note that we are using local where-defined functions.
test-20f : ∀ m n → Vec (Vec ℕ n) m → Vec (Vec ℕ m) n
test-20f 0       n []       = repl []
  where
    repl : ∀ {k} → Vec ℕ 0 → Vec _ k
    repl {0} x     = []
    repl {suc _} x = x ∷ repl x
test-20f (suc _) n (x ∷ xs) = xzip x (test-20f _ n xs)
  where
    xzip : ∀ {n} → Vec _ n → Vec _ n → Vec _ n
    xzip []       []       = []
    xzip (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ xzip xs ys

test₂₀ : kompile test-20f [] [] ≡ ok _
test₂₀ = refl

-- Make sure that we can handle lists of hom. objects
test-21f : ∀ n → List (Vec ℕ n)
test-21f n = []

test₂₁ : kompile test-21f [] [] ≡ ok _
test₂₁ = refl

-- Test that cons and friends work on a simple example
test-22f : ∀ n → Vec (Vec ℕ n) 1
test-22f n = repl 0 ∷ []
 where
    repl : ∀ {m} → ℕ → Vec ℕ m
    repl {0} x     = []
    repl {suc _} x = x ∷ repl x

test₂₂ : kompile test-22f [] [] ≡ ok _
test₂₂ = refl

-- Test that polymorphic functions are failing with a reasonable error
test-23f : ∀ {X : Set} → X → X
test-23f x = x

test₂₃ : kompile test-23f [] [] ≡ error _
test₂₃ = refl


-- FIXME: This gives a buggy assertion on the argument (that is not present)
test-24f : Vec ℕ (1 + 2)
test-24f = 1 ∷ 2 ∷ 3 ∷ []

test₂₄ : kompile test-24f [] [] ≡ ok _
test₂₄ = refl

-- Array stuff
test-25f : ℕ → Ar ℕ 1 V.[ 5 ]
test-25f n = cst n

test₂₅ : kompile test-25f [] [] ≡ ok _
test₂₅ = refl

-- Element-wise addition.
test-26f : ∀ {d s} → (a b : Ar ℕ d s) → Ar ℕ d s
test-26f a b = imap λ iv → sel a iv + sel b iv

test₂₆ : kompile test-26f [] [] ≡ ok _
test₂₆ = refl
