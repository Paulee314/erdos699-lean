/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 Paul Lee.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adaptation notice: the statement below is `Erdos699.erdos_699` from
google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/699.lean`
(commit `f153efa8fdc078131e214547781d631e2d257daf`), with the extra hypothesis `j ^ 2 < n`.
-/
module

public import Mathlib

/-!
# Erdős Problem 699 when `j² < n`

Erdős Problem 699 (<https://www.erdosproblems.com/699>; Erdős and Szekeres, *Some number
theoretic problems on binomial coefficients*, Austral. Math. Soc. Gaz. 5 (1978), 97–99) asks
whether for every `1 ≤ i < j ≤ n / 2` there is a prime `p ≥ i` dividing
`gcd(C(n, i), C(n, j))`. The problem is open.

`erdos_699.variants.of_sq_lt` states that the answer is yes whenever `j² < n`; equivalently,
every counterexample `(n, i, j)` has `n ≤ j²`. The statement is the formal-conjectures statement
of the problem with the single extra hypothesis `j ^ 2 < n`.
-/

@[expose] public section

namespace Erdos699

/--
Erdős Problem 699 holds when $j^2 < n$: for $1 \le i < j \le n / 2$ with $j^2 < n$ there is a
prime $p \ge i$ with $p \mid \gcd\big(\binom{n}{i}, \binom{n}{j}\big)$.
-/
theorem erdos_699.variants.of_sq_lt :
    ∀ n i j : ℕ,
      1 ≤ i →
      i < j →
      j ≤ n / 2 →
      j ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  sorry

end Erdos699
