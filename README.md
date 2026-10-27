# Erdős Problem 699 in Lean: every counterexample has n ≤ j²

[Erdős Problem 699](https://www.erdosproblems.com/699) (Erdős and Szekeres, 1978) asks: for every
1 ≤ i < j ≤ n/2, is there a prime p ≥ i that divides both C(n, i) and C(n, j)? The problem is open.

This repository proves in Lean 4 with Mathlib that the answer is yes whenever j² < n. Equivalently,
any counterexample (n, i, j) has n ≤ j². It is packaged for [Palomar](https://palomar-registry.org/).
The statement is the one in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f153efa8fdc078131e214547781d631e2d257daf/FormalConjectures/ErdosProblems/699.lean)
with the single extra hypothesis `j ^ 2 < n`.

| Lean name | Statement |
|---|---|
| `Erdos699.erdos_699.variants.of_sq_lt` | If 1 ≤ i < j ≤ n/2 and j² < n, some prime p ≥ i divides gcd(C(n, i), C(n, j)). |

## The argument

Let g = gcd(C(n, i), C(n, j)) and suppose every prime factor of g is below i.

1. **Lower bound** (Erdős and Szekeres). The identity C(n, j) C(j, i) = C(n, i) C(n − i, j − i)
   shows that C(n, i) divides g · C(j, i). So g ≥ C(n, i)/C(j, i) ≥ (n/j)^i.
2. **Upper bound.** For every prime p, the power of p in C(n, i) is at most ⌊log_p n⌋ (Kummer), so
   p^(v_p(g)) ≤ n. There are at most i/2 primes below i. So g ≤ n^(i/2).
3. Together, (n/j)^i ≤ n^(i/2), which gives n ≤ j².

## Why it matters

The bound reduces the problem to j ≥ √n. Combined with a computer search of every n < 10^12, it
rules out counterexamples with j ≤ 10^6 for every n, and with a further enumeration, j ≤ 10^9; see
[Paulee314/erdos699](https://github.com/Paulee314/erdos699). Those computations are not part of this
formalization. The bound itself follows in a few lines
from the Erdős–Szekeres inequality and may well be folklore.

## Files

| Path | Content |
|---|---|
| `Challenge.lean` | The statement, with `sorry`. This is the file to audit. |
| `Solution.lean` | The same declaration, proved. It does not import `Challenge.lean`. |
| `Erdos699/Basic.lean` | The proof: the Erdős–Szekeres divisibility, C(j, i) n^i ≤ C(n, i) j^i, the Kummer bound, the count of primes below i, and `le_sq_of_counterexample` (n ≤ j²). |
| `AxiomAudit.lean` | `#print axioms` for the main results. Each uses only `propext`, `Classical.choice` and `Quot.sound`. |
| `comparator.json` | The theorem Comparator compares between `Challenge` and `Solution`. |
| `formalization.yaml` | Provenance, sources, automation and review record. |

## Building

Lean `v4.36.0-rc1` and Mathlib at the matching tag (pinned in `lake-manifest.json`).

```
lake exe cache get   # prebuilt Mathlib
lake build           # builds Challenge (one intentional sorry), the proof, Solution and AxiomAudit
```

The fully elaborated type (`set_option pp.all true`) of the theorem is identical in the `Challenge`
and `Solution` environments.

## Provenance and AI use

The Lean code, including the statement, was written by an AI agent (Claude, Anthropic) at the
author's direction, compiling against Lean and iterating on the errors. The author chose what to
formalize and published the result; he did not write the Lean code by hand and is not a professional
mathematician. No human expert has reviewed this work. See `formalization.yaml` for details.

## License

Apache License 2.0 (`LICENSE`). The statement is adapted from google-deepmind/formal-conjectures,
also Apache 2.0; see the notices at the top of `Challenge.lean`, `Solution.lean` and
`Erdos699/Basic.lean`.
