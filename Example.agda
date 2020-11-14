open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)
open import Data.Nat
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
open import Structures
open import Function


bar : ℕ → ℕ
bar x = 0

foo : ℕ → ℕ
foo x = 1 + x

test₁ : kompile foo [] [] ≡ (ok $ "// Function Example.foo\n"
                               ++ "int\n"
                               ++ "Example_foo(int x_1) {\n"
                               ++ "int __ret;\n"
                               ++ "x = x_1;\n"
                               ++ "__ret = (1 + x);\n"
                               ++ "return __ret;\n"
                               ++ "}\n\n\n\n")
test₁ = refl


test₂ : kompile bar [] [] ≡ (ok $ "// Function Example.bar\n"
                               ++ "int\n"
                               ++ "Example_bar(int x_1) {\n"
                               ++ "int __ret;\n"
                               ++ "x = x_1;\n"
                               ++ "__ret = 0;\n"
                               ++ "return __ret;\n"
                               ++ "}\n\n\n\n")
test₂ = refl
