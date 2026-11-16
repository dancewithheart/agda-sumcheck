{-# OPTIONS --safe --without-K #-}
module Examples where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Sumcheck

-- p(x,y) = 1 + x + 2y + xy over F₅; its Boolean-hypercube sum is 1.
polynomial : F → F → F
polynomial x y = add f1 (add x (add (mul f2 y) (mul x y)))

oracle : List F → F
oracle (x ∷ y ∷ []) = polynomial x y
oracle _ = f0

hypercube-sum : add (polynomial f0 f0)
  (add (polynomial f0 f1) (add (polynomial f1 f0) (polynomial f1 f1))) ≡ f1
hypercube-sum = refl

-- Round 0: [4,2], r=2; round 1: [3,2], r=3.
honest : List Message
honest = round f4 f2 f2 ∷ round f3 f2 f3 ∷ []

honest-accepted : verify oracle 2 f1 honest ≡ true
honest-accepted = refl

wrong-claim-rejected : verify oracle 2 f2 honest ≡ false
wrong-claim-rejected = refl

wrong-round-rejected : verify oracle 2 f1
  (round f4 f2 f2 ∷ round f3 f1 f3 ∷ []) ≡ false
wrong-round-rejected = refl

wrong-final-rejected : verify (λ _ → f1) 2 f1 honest ≡ false
wrong-final-rejected = refl

short-transcript-rejected : verify oracle 2 f1 (round f4 f2 f2 ∷ []) ≡ false
short-transcript-rejected = refl

long-transcript-rejected : verify oracle 1 f1 honest ≡ false
long-transcript-rejected = refl

at-first-node : interpolate f3 f1 f0 ≡ f3
at-first-node = refl

at-second-node : interpolate f3 f1 f1 ≡ f1
at-second-node = refl

-- Sumcheck has probabilistic soundness, not universal soundness for fixed
-- challenges. Here a false claim is accepted because the first challenge is 0.
dishonest-fixed-challenge-accepted : verify oracle 2 f2
  (round f4 f3 f0 ∷ round f1 f3 f1 ∷ []) ≡ true
dishonest-fixed-challenge-accepted = refl

-- z-lean's EvalFormTests Example1 uses 1 + 2x over ZMod 17. At the
-- Boolean nodes its checked golden values 1, 3 and total 4 also agree in F₅.
linearOracle : List F → F
linearOracle (x ∷ []) = add f1 (mul f2 x)
linearOracle _ = f0

lean-example-value0 : linearOracle (f0 ∷ []) ≡ f1
lean-example-value0 = refl

lean-example-value1 : linearOracle (f1 ∷ []) ≡ f3
lean-example-value1 = refl

lean-example-claim : add (linearOracle (f0 ∷ [])) (linearOracle (f1 ∷ [])) ≡ f4
lean-example-claim = refl

lean-example-accepts : verify linearOracle 1 f4 (round f1 f3 f1 ∷ []) ≡ true
lean-example-accepts = refl
