{-# OPTIONS --safe --without-K #-}
module Sumcheck where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

infixr 5 _+++_
infixr 3 _&&_

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

_+++_ : {A : Set} → List A → List A → List A
[] +++ ys = ys
(x ∷ xs) +++ ys = x ∷ (xs +++ ys)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs +++ (x ∷ [])

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- Toy field F₅
data F : Set where
  f0 f1 f2 f3 f4 : F

next : F → F
next f0 = f1
next f1 = f2
next f2 = f3
next f3 = f4
next f4 = f0

add : F → F → F
add x f0 = x
add x f1 = next x
add x f2 = next (next x)
add x f3 = next (next (next x))
add x f4 = next (next (next (next x)))

neg : F → F
neg f0 = f0
neg f1 = f4
neg f2 = f3
neg f3 = f2
neg f4 = f1

sub : F → F → F
sub x y = add x (neg y)

mul : F → F → F
mul x f0 = f0
mul x f1 = x
mul x f2 = add x x
mul x f3 = add (add x x) x
mul x f4 = add (add (add x x) x) x

same : F → F → Bool
same f0 f0 = true
same f1 f1 = true
same f2 f2 = true
same f3 f3 = true
same f4 f4 = true
same _ _ = false

same-refl : (x : F) → same x x ≡ true
same-refl f0 = refl
same-refl f1 = refl
same-refl f2 = refl
same-refl f3 = refl
same-refl f4 = refl

same-sound : (x y : F) → same x y ≡ true → x ≡ y
same-sound f0 f0 p = refl
same-sound f0 f1 ()
same-sound f0 f2 ()
same-sound f0 f3 ()
same-sound f0 f4 ()
same-sound f1 f0 ()
same-sound f1 f1 p = refl
same-sound f1 f2 ()
same-sound f1 f3 ()
same-sound f1 f4 ()
same-sound f2 f0 ()
same-sound f2 f1 ()
same-sound f2 f2 p = refl
same-sound f2 f3 ()
same-sound f2 f4 ()
same-sound f3 f0 ()
same-sound f3 f1 ()
same-sound f3 f2 ()
same-sound f3 f3 p = refl
same-sound f3 f4 ()
same-sound f4 f0 ()
same-sound f4 f1 ()
same-sound f4 f2 ()
same-sound f4 f3 ()
same-sound f4 f4 p = refl

and-left : {a b : Bool} → (a && b) ≡ true → a ≡ true
and-left {true} p = refl
and-left {false} ()

and-right : {a b : Bool} → (a && b) ≡ true → b ≡ true
and-right {true} p = p
and-right {false} ()

-- A small reusable proof by exhaustive computation over F₅.
allF : (F → Bool) → Bool
allF p = p f0 && p f1 && p f2 && p f3 && p f4

allF-elim : (p : F → Bool) (x : F) → allF p ≡ true → p x ≡ true
allF-elim p f0 h = and-left {a = p f0} {b = p f1 && p f2 && p f3 && p f4} h
allF-elim p f1 h = and-left {a = p f1} {b = p f2 && p f3 && p f4} (and-right {a = p f0} {b = p f1 && p f2 && p f3 && p f4} h)
allF-elim p f2 h = and-left {a = p f2} {b = p f3 && p f4} (and-right {a = p f1} {b = p f2 && p f3 && p f4} (and-right {a = p f0} {b = p f1 && p f2 && p f3 && p f4} h))
allF-elim p f3 h = and-left {a = p f3} {b = p f4} (and-right {a = p f2} {b = p f3 && p f4} (and-right {a = p f1} {b = p f2 && p f3 && p f4} (and-right {a = p f0} {b = p f1 && p f2 && p f3 && p f4} h)))
allF-elim p f4 h = (and-right {a = p f3} {b = p f4} (and-right {a = p f2} {b = p f3 && p f4} (and-right {a = p f1} {b = p f2 && p f3 && p f4} (and-right {a = p f0} {b = p f1 && p f2 && p f3 && p f4} h))))

all3 : (p : F → F → F → Bool) →
  allF (λ x → allF (λ y → allF (p x y))) ≡ true →
  (x y z : F) → p x y z ≡ true
all3 p h x y z =
  allF-elim (p x y) z (allF-elim (λ y' → allF (p x y')) y
    (allF-elim (λ x' → allF (λ y' → allF (p x' y'))) x h))

-- Executable linear interpolation at nodes 0 and 1.
interpolate : F → F → F → F
interpolate y0 y1 r = add y0 (mul (sub y1 y0) r)

-- Independent Lagrange specification: (1 - r) * y0 + r * y1.
lagrange : F → F → F → F
lagrange y0 y1 r = add (mul (sub f1 r) y0) (mul r y1)

interpolate-is-lagrange : (y0 y1 r : F) → interpolate y0 y1 r ≡ lagrange y0 y1 r
interpolate-is-lagrange y0 y1 r = same-sound _ _
  (all3 (λ a b c → same (interpolate a b c) (lagrange a b c)) refl y0 y1 r)

-- For every coefficient pair, interpolation of its 0/1 evaluations equals
-- evaluation of the original polynomial a + b*r, including r = 0 and r = 1.
interpolate-linear : (a b r : F) →
  interpolate a (add a b) r ≡ add a (mul b r)
interpolate-linear a b r = same-sound _ _
  (all3 (λ x y z → same (interpolate x (add x y) z) (add x (mul y z))) refl a b r)

-- Each message fixes a degree-at-most-one round polynomial by its two values.
-- The challenge is supplied externally and must be sampled independently in a
-- real interactive protocol; it is stored here to replay a transcript.
data Message : Set where
  round : (at0 at1 challenge : F) → Message

-- The reversed prefix is internal; the final oracle receives challenges in
-- their original order. Wrong transcript lengths reject.
verifyWith : (F → F → F → F) → (List F → F) → Nat → List F → F → List Message → Bool
verifyWith eval oracle zero seen claim [] = same claim (oracle (reverse seen))
verifyWith eval oracle zero seen claim (_ ∷ _) = false
verifyWith eval oracle (suc n) seen claim [] = false
verifyWith eval oracle (suc n) seen claim (round y0 y1 r ∷ rest) =
  same claim (add y0 y1) && verifyWith eval oracle n (r ∷ seen) (eval y0 y1 r) rest

verify : (List F → F) → Nat → F → List Message → Bool
verify oracle n claim transcript = verifyWith interpolate oracle n [] claim transcript

-- Mathematical specification, independent of the optimized interpolation.
specVerify : (List F → F) → Nat → F → List Message → Bool
specVerify oracle n claim transcript = verifyWith lagrange oracle n [] claim transcript

agree : (oracle : List F → F) (n : Nat) (seen : List F) (claim : F) (transcript : List Message) →
  verifyWith interpolate oracle n seen claim transcript ≡ verifyWith lagrange oracle n seen claim transcript
agree oracle zero seen claim [] = refl
agree oracle zero seen claim (_ ∷ _) = refl
agree oracle (suc n) seen claim [] = refl
agree oracle (suc n) seen claim (round y0 y1 r ∷ rest)
  rewrite interpolate-is-lagrange y0 y1 r =
  cong (λ result → same claim (add y0 y1) && result)
    (agree oracle n (r ∷ seen) (lagrange y0 y1 r) rest)

-- Acceptance as a relation, separate from the Boolean implementation.
data Accepts (oracle : List F → F) : Nat → List F → F → List Message → Set where
  final : {seen : List F} {claim : F} → claim ≡ oracle (reverse seen) →
    Accepts oracle zero seen claim []
  step : {n : Nat} {seen : List F} {claim y0 y1 r : F} {rest : List Message} →
    claim ≡ add y0 y1 → Accepts oracle n (r ∷ seen) (lagrange y0 y1 r) rest →
    Accepts oracle (suc n) seen claim (round y0 y1 r ∷ rest)

spec-sound : (oracle : List F → F) (n : Nat) (seen : List F) (claim : F) (transcript : List Message) →
  verifyWith lagrange oracle n seen claim transcript ≡ true → Accepts oracle n seen claim transcript
spec-sound oracle zero seen claim [] h = final (same-sound claim (oracle (reverse seen)) h)
spec-sound oracle zero seen claim (_ ∷ _) ()
spec-sound oracle (suc n) seen claim [] ()
spec-sound oracle (suc n) seen claim (round y0 y1 r ∷ rest) h =
  step (same-sound claim (add y0 y1) (and-left h))
    (spec-sound oracle n (r ∷ seen) (lagrange y0 y1 r) rest (and-right h))

spec-complete : {oracle : List F → F} {n : Nat} {seen : List F} {claim : F} {transcript : List Message} →
  Accepts oracle n seen claim transcript → verifyWith lagrange oracle n seen claim transcript ≡ true
spec-complete (final {claim = claim} refl) = same-refl claim
spec-complete (step {y0 = y0} {y1 = y1} refl rest)
  rewrite same-refl (add y0 y1) | spec-complete rest = refl

verify-sound : (oracle : List F → F) (n : Nat) (claim : F) (transcript : List Message) →
  verify oracle n claim transcript ≡ true → Accepts oracle n [] claim transcript
verify-sound oracle n claim transcript h = spec-sound oracle n [] claim transcript
  (trans (sym (agree oracle n [] claim transcript)) h)

verify-complete : (oracle : List F → F) (n : Nat) (claim : F) (transcript : List Message) →
  Accepts oracle n [] claim transcript → verify oracle n claim transcript ≡ true
verify-complete oracle n claim transcript h =
  trans (agree oracle n [] claim transcript) (spec-complete h)

-- Quest 12's per-query agreement principle, specialized to the one final
-- query made by this verifier. It does not assume function extensionality.
verifyWith-oracle-cong : (eval : F → F → F → F) (left right : List F → F) →
  ((point : List F) → left point ≡ right point) →
  (n : Nat) (seen : List F) (claim : F) (transcript : List Message) →
  verifyWith eval left n seen claim transcript ≡ verifyWith eval right n seen claim transcript
verifyWith-oracle-cong eval left right same-query zero seen claim []
  rewrite same-query (reverse seen) = refl
verifyWith-oracle-cong eval left right same-query zero seen claim (_ ∷ _) = refl
verifyWith-oracle-cong eval left right same-query (suc n) seen claim [] = refl
verifyWith-oracle-cong eval left right same-query (suc n) seen claim (round y0 y1 r ∷ rest) =
  cong (λ result → same claim (add y0 y1) && result)
    (verifyWith-oracle-cong eval left right same-query n (r ∷ seen) (eval y0 y1 r) rest)

verify-oracle-cong : (left right : List F → F) →
  ((point : List F) → left point ≡ right point) →
  (n : Nat) (claim : F) (transcript : List Message) →
  verify left n claim transcript ≡ verify right n claim transcript
verify-oracle-cong left right same-query n claim transcript =
  verifyWith-oracle-cong interpolate left right same-query n [] claim transcript
