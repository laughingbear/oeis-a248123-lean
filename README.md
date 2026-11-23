# OEIS A248123: a(n) exists for every n > 0

A Lean 4 proof of Zhi-Wei Sun's conjecture on [OEIS A248123](https://oeis.org/A248123): for every
`n > 0` there is `m > 0` with `gcd(m, n) = 1` and `m * n ∣ C(m + n)`, where `C(k)` is the `k`-th
Catalan number.

The main theorem `A248123.conjecture` has the same statement and definitions as
`OeisA248123.conjecture` in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/248123.lean).

## Proof

The argument follows Zedan Soorya's comment on the OEIS entry (Nov 13 2026), with a simpler
choice of residues. Take primes `u < r` with `u > 2n + 1`, `3u ≤ 2r < 4u`, and put
`N = r * u + n`, `m = r * u`. Choose the residue of `N` so that `N ≡ -2` modulo the square of the
odd part of `n`, and `N ≡ -3` modulo `4` times the `2`-part of `n`. Kummer's theorem
(`padicValNat_choose`) then shows that `n`, `r` and `u` all divide `C(N)`.

* `u` comes from Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_modEq`, Mathlib).
* `r` comes from the prime number theorem in arithmetic progressions
  (`chebyshev_asymptotic_pnt`,
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)).

## Build

```bash
lake exe cache get
lake build
```

## Checks

`#print axioms A248123.conjecture` gives `[propext, Classical.choice, Quot.sound]`.
`chebyshev_asymptotic_pnt` at the pinned PrimeNumberTheoremAnd commit has the same axioms.
