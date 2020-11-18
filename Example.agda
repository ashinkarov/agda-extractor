{-# OPTIONS --rewriting #-}
open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import Function

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-identityʳ #-}


test1-f : ℕ → ℕ
test1-f x = 1 + x

test₁ : kompile test1-f [] [] ≡ (ok $ "// Function Example.test1-f\n"
                                   ++ "int\n"
                                   ++ "Example_test1_f(int x_1) {\n"
                                   ++ "int __ret;\n"
                                   ++ "x = x_1;\n"
                                   ++ "__ret = (1 + x);\n"
                                   ++ "return __ret;\n"
                                   ++ "}\n\n\n\n")
test₁ = refl


test2-f : ℕ → ℕ
test2-f x = 0

test₂ : kompile test2-f [] [] ≡ (ok $ "// Function Example.test2-f\n"
                                   ++ "int\n"
                                   ++ "Example_test2_f(int x_1) {\n"
                                   ++ "int __ret;\n"
                                   ++ "x = x_1;\n"
                                   ++ "__ret = 0;\n"
                                   ++ "return __ret;\n"
                                   ++ "}\n\n\n\n")
test₂ = refl


-- Rewriting test
test3-f : ℕ → ℕ
test3-f x = x + 0

test₃ : kompile test3-f [] [] ≡ (ok $ "// Function Example.test3-f\n"
                                   ++ "int\n"
                                   ++ "Example_test3_f(int x_1) {\n"
                                   ++ "int __ret;\n"
                                   ++ "x = x_1;\n"
                                   ++ "__ret = x;\n"
                                   ++ "return __ret;\n"
                                   ++ "}\n\n\n\n")
test₃ = refl


-- Make sure that we can deal with functions inside
-- the type and properly collect them while extraction.
test-4h : ℕ → ℕ
test-4h x = 1 + x

test-4f : Fin (test-4h 3) → Fin 4
test-4f a = zero

test₄ : kompile test-4f (quote test-4h ∷ []) [] ≡ ok _
test₄ = refl


-- Test if we can deal with multiple patterns.
module _ where
  test-5f : ℕ → ℕ
  test-5f (suc (suc x)) = x
  test-5f _ = 0

  test₅ : kompile test-5f [] [] ≡ ok _
  test₅ = refl


  test-6f : Fin 5 → Fin 3
  test-6f (suc (suc x)) = x
  test-6f _ = zero


-- Make sure that we are compiling multi-argument function correctly
test-7f : (a b c : ℕ) → ℕ
test-7f a b c = c

test₇ : kompile test-7f [] [] ≡ (ok $ "// Function Example.test-7f\nint\nExample_test_7f(int x_1, int x_2, int x_3) {\n"
                                   ++ "int __ret;\na = x_1;\nb = x_2;\nc = x_3;\n__ret = c;\nreturn __ret;\n}\n\n\n\n")
test₇ = refl
