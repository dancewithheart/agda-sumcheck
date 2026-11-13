{-# OPTIONS --safe --without-K #-}
module FieldLaws where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Sumcheck

toNat : F → Nat
toNat f0 = 0
toNat f1 = 1
toNat f2 = 2
toNat f3 = 3
toNat f4 = 4

-- Successive naturals cycle through 0,1,2,3,4: reduction modulo five.
fromNat : Nat → F
fromNat zero = f0
fromNat (suc n) = next (fromNat n)

roundtrip : (x : F) → fromNat (toNat x) ≡ x
roundtrip f0 = refl
roundtrip f1 = refl
roundtrip f2 = refl
roundtrip f3 = refl
roundtrip f4 = refl

all2 : (p : F → F → Bool) →
  allF (λ x → allF (p x)) ≡ true → (x y : F) → p x y ≡ true
all2 p h x y = allF-elim (p x) y (allF-elim (λ x' → allF (p x')) x h)

add-mod-five : (x y : F) → add x y ≡ fromNat (toNat x + toNat y)
add-mod-five x y = same-sound _ _
  (all2 (λ a b → same (add a b) (fromNat (toNat a + toNat b))) refl x y)

mul-mod-five : (x y : F) → mul x y ≡ fromNat (toNat x * toNat y)
mul-mod-five x y = same-sound _ _
  (all2 (λ a b → same (mul a b) (fromNat (toNat a * toNat b))) refl x y)

add-neg : (x : F) → add x (neg x) ≡ f0
add-neg x = same-sound _ _ (allF-elim (λ y → same (add y (neg y)) f0) x refl)
