{-# OPTIONS --safe --without-K #-}
module Quest12Bridge where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Sumcheck

-- Adapted from Quest 12 TransformFusion.dot-acc / dot-transport. Paired
-- entries keep the two input vectors aligned without importing stdlib Vec.
record Pair (A B : Set) : Set where
  constructor _,_
  field first : A
        second : B
open Pair public

mapPairs : {A B : Set} → (A → B) → List (Pair A A) → List (Pair B B)
mapPairs φ [] = []
mapPairs φ ((x , y) ∷ xs) = (φ x , φ y) ∷ mapPairs φ xs

module DotTransport {R S : Set}
  (zeroR : R) (addR mulR : R → R → R)
  (zeroS : S) (addS mulS : S → S → S)
  (φ : R → S)
  (φ-zero : φ zeroR ≡ zeroS)
  (φ-add : (x y : R) → φ (addR x y) ≡ addS (φ x) (φ y))
  (φ-mul : (x y : R) → φ (mulR x y) ≡ mulS (φ x) (φ y)) where

  foldR : R → List (Pair R R) → R
  foldR acc [] = acc
  foldR acc ((x , y) ∷ xs) = foldR (addR acc (mulR x y)) xs

  foldS : S → List (Pair S S) → S
  foldS acc [] = acc
  foldS acc ((x , y) ∷ xs) = foldS (addS acc (mulS x y)) xs

  dotR : List (Pair R R) → R
  dotR = foldR zeroR

  dotS : List (Pair S S) → S
  dotS = foldS zeroS

  dot-acc : (acc : R) (xs : List (Pair R R)) →
    φ (foldR acc xs) ≡ foldS (φ acc) (mapPairs φ xs)
  dot-acc acc [] = refl
  dot-acc acc ((x , y) ∷ xs) =
    trans (dot-acc (addR acc (mulR x y)) xs)
      (cong (λ start → foldS start (mapPairs φ xs))
        (trans (φ-add acc (mulR x y)) (cong (addS (φ acc)) (φ-mul x y))))

  dot-transport : (xs : List (Pair R R)) → φ (dotR xs) ≡ dotS (mapPairs φ xs)
  dot-transport xs = trans (dot-acc zeroR xs)
    (cong (λ start → foldS start (mapPairs φ xs)) φ-zero)

pairAdd pairMul : Pair F F → Pair F F → Pair F F
pairAdd (x , x') (y , y') = (add x y , add x' y')
pairMul (x , x') (y , y') = (mul x y , mul x' y')

module Projection = DotTransport (f0 , f0) pairAdd pairMul f0 add mul first
  refl (λ _ _ → refl) (λ _ _ → refl)

-- Interpolation's Lagrange form is a two-term dot product.
dot-is-lagrange : (a b r : F) →
  Projection.dotS ((sub f1 r , a) ∷ (r , b) ∷ []) ≡ lagrange a b r
dot-is-lagrange a b r = same-sound _ _
  (all3 (λ x y z → same (Projection.dotS ((sub f1 z , x) ∷ (z , y) ∷ []))
    (lagrange x y z)) refl a b r)

-- Compute two independent interpolations together, then project the first.
-- Quest 12's transport proof justifies that this equals the scalar result.
projected-interpolation : (a b r a' b' r' : F) →
  first (Projection.dotR
    (((sub f1 r , sub f1 r') , (a , a')) ∷ ((r , r') , (b , b')) ∷ [])) ≡ lagrange a b r
projected-interpolation a b r a' b' r' =
  trans (Projection.dot-transport
    (((sub f1 r , sub f1 r') , (a , a')) ∷ ((r , r') , (b , b')) ∷ []))
    (dot-is-lagrange a b r)
