module Ch7 where

open import Agda.Builtin.Nat hiding (_<_)
open import Agda.Builtin.Unit

data ⊥ : Set where

_>=_ : Nat → Nat → Set
_ >= zero = ⊤
zero >= suc n = ⊥
suc m >= suc n = m >= n

_>_ : Nat → Nat → Set
m > n = m >= suc n

_<_ : Nat → Nat → Set
m < n = n > m

data DivDom : Nat → Nat → Set where
  div-dom-lt : (m n : Nat) → m < n → DivDom m n
  div-dom-geq : (m n : Nat) → m >= n → DivDom (m - n) n → DivDom m n

div : (m n : Nat) → DivDom m n → Nat
div .m .n (div-dom-lt m n p) = zero
div .m .n (div-dom-geq m n p q) = 1 + div (m - n) n q
