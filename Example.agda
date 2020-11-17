{-# OPTIONS --rewriting #-}
open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_)
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

