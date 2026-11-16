# Sumcheck in Agda

An executable sumcheck verifier over F₅ (integers modulo 5), with correctness proofs checked by Agda.

## How it works

Suppose we have a polynomial:

```
p(x,y) = 1 + x + 2y + xy
```

Someone claims its sum over all Boolean inputs is 1:

```
p(0,0) + p(0,1) + p(1,0) + p(1,1) = 1 (mod 5)
```

Instead of evaluating every input, the verifier checks a sequence of smaller claims.

**Round 1**

The prover supplies two evaluations of a linear polynomial:

```
g₁(0) = 4
g₁(1) = 2
```

The verifier checks `4 + 2 = 1 (mod 5)`.

It then chooses a challenge `r₁ = 2`. Linear interpolation gives `g₁(2) = 0`.

**Round 2**

The prover supplies another pair:

```
g₂(0) = 3
g₂(1) = 2
```

The verifier checks `3 + 2 = 0 (mod 5)`.

With the next challenge `r₂ = 3`, interpolation gives `g₂(3) = 0`.

Finally, the verifier evaluates `p(2,3) = 0`.

Example is in [`honest-accepted`](src/Examples.agda).

The sum-check protocol was introduced by Lund, Fortnow, Karloff and Nisan (1992). See [Thaler, 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) for the protocol and its soundness analysis.

## Modules

- [`Sumcheck.agda`](src/Sumcheck.agda):
  - F5 arithmetic and linear interpolation.
  - Transcript verification, including round consistency and final oracle evaluation.
  - Proofs connecting the executable checker to its mathematical specification.
  - `interpolate-is-lagrange`: our interpolation function agrees with the standard Lagrange formula.
  - `verify-sound` and `verify-complete`: the checker accepts exactly the transcripts satisfying its acceptance specification.
- [`FieldLaws.agda`](src/FieldLaws.agda) - arithmetic modulo 5.
- [`Examples.agda`](src/Examples.agda) - accepted and rejected transcripts, including a false claim accepted with fixed challenges.
- [`Quest12Bridge.agda`](src/Quest12Bridge.agda) - dot-product transport reused from other experiment.

* Check proofs

```sh
agda -i src src/Examples.agda
agda -i src src/Sumcheck.agda
```


* Limitations

Supports only linear round polynomials over F5.  
Challenges are provided externally.  
No probabilistic soundness, zero knowledge, correctness of extracted code.

See [`dishonest-fixed-challenge-accepted`](src/Examples.agda) for why challenge selection matters.

* References

- Lund, Fortnow, Karloff, Nisan (1992). [Algebraic Methods for Interactive Proof Systems](https://doi.org/10.1145/146585.146605).
- Justin Thaler. [Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), §2.4 (interpolation), §4.1 (sumcheck).
- [z-lean](https://github.com/z-tech/z-lean) - Lean sumcheck formalization that motivated this experiment.