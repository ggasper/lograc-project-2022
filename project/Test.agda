module Test where

open import Data.Nat

foo : ℕ
foo = 45

open import Level renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor.Algebra

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero
