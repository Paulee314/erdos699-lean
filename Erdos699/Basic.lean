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

Adaptation notice: the conclusion of `of_sq_lt` is the statement of `Erdos699.erdos_699` in
google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/699.lean`
(commit `f153efa8fdc078131e214547781d631e2d257daf`). Everything else in this file is new.
-/
module

public import Mathlib

/-!
# Erdős Problem 699: every counterexample has `n ≤ j²`

Erdős Problem 699 asks whether for every `1 ≤ i < j ≤ n / 2` some prime `p ≥ i` divides
`g = gcd(C(n, i), C(n, j))`. This file proves that the answer is yes whenever `j² < n`.

The proof has three steps.

* `choose_dvd_gcd_mul`: the identity `C(n, j) C(j, i) = C(n, i) C(n - i, j - i)` gives
  `C(n, i) ∣ g · C(j, i)`, so `g ≥ C(n, i) / C(j, i)` (Erdős and Szekeres, 1978).
* `choose_mul_pow_le`: `C(n, i) / C(j, i) ≥ (n / j)^i`, in the form `C(j, i) n^i ≤ C(n, i) j^i`.
* `le_pow_card_of_dvd_choose`, `two_mul_card_le`: if every prime factor of `g` is below `i`,
  then `g ≤ n^c` with `2c ≤ i`. Each prime power `p^a ∥ g` satisfies `p^a ≤ n` because
  `v_p(C(n, i)) ≤ ⌊log_p n⌋` (Kummer), and there are at most `i / 2` primes below `i`.

Together, `n^i ≤ n^c j^i` with `2c ≤ i`, hence `n^i ≤ j^{2i}` and `n ≤ j²`.
-/

@[expose] public section

namespace Erdos699

/-- For `j ≤ n`: `j(j-1)⋯(j-i+1) · n^i ≤ n(n-1)⋯(n-i+1) · j^i`. -/
theorem descFactorial_mul_pow_le {j n : ℕ} (hjn : j ≤ n) :
    ∀ i : ℕ, j.descFactorial i * n ^ i ≤ n.descFactorial i * j ^ i
  | 0 => by simp
  | i + 1 => by
    have ih := descFactorial_mul_pow_le hjn i
    have key : (j - i) * n ≤ (n - i) * j := by
      rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n j]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hjn) _
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc (j - i) * j.descFactorial i * (n ^ i * n)
        = ((j - i) * n) * (j.descFactorial i * n ^ i) := by ring
      _ ≤ ((n - i) * j) * (n.descFactorial i * j ^ i) := Nat.mul_le_mul key ih
      _ = (n - i) * n.descFactorial i * (j ^ i * j) := by ring

/-- For `j ≤ n`: `C(j, i) · n^i ≤ C(n, i) · j^i`, i.e. `C(n, i) / C(j, i) ≥ (n / j)^i`. -/
theorem choose_mul_pow_le {i j n : ℕ} (hjn : j ≤ n) :
    j.choose i * n ^ i ≤ n.choose i * j ^ i := by
  have h := descFactorial_mul_pow_le hjn i
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos i)

/-- The identity `C(n, j) C(j, i) = C(n, i) C(n - i, j - i)` gives
`C(n, i) ∣ gcd(C(n, i), C(n, j)) · C(j, i)` (Erdős and Szekeres). -/
theorem choose_dvd_gcd_mul {n i j : ℕ} (hij : i ≤ j) :
    n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
  rw [← Nat.gcd_mul_right]
  refine Nat.dvd_gcd (Nat.dvd_mul_right _ _) ?_
  rw [Nat.choose_mul (n := n) hij]
  exact Nat.dvd_mul_right _ _

/-- A divisor `g` of `C(n, i)`, with `i ≤ n`, is at most `n ^ ω(g)`, because
`p ^ v_p(C(n, i)) ≤ n` for every prime `p` (Kummer). -/
theorem le_pow_card_of_dvd_choose {g n i : ℕ} (hn : n ≠ 0) (hg : g ≠ 0) (hin : i ≤ n)
    (hdvd : g ∣ n.choose i) : g ≤ n ^ g.primeFactors.card := by
  have hc : n.choose i ≠ 0 := (Nat.choose_pos hin).ne'
  calc g = g.factorization.prod (fun p k => p ^ k) := (Nat.prod_factorization_pow_eq_self hg).symm
    _ = ∏ p ∈ g.primeFactors, p ^ g.factorization p := by
        rw [Finsupp.prod, Nat.support_factorization]
    _ ≤ ∏ _p ∈ g.primeFactors, n := by
        refine Finset.prod_le_prod (fun p hp => ?_)
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        calc p ^ g.factorization p ≤ p ^ (n.choose i).factorization p :=
              Nat.pow_le_pow_right hp'.pos ((Nat.factorization_le_iff_dvd hg hc).2 hdvd p)
          _ ≤ p ^ Nat.log p n := Nat.pow_le_pow_right hp'.pos Nat.factorization_choose_le_log
          _ ≤ n := Nat.pow_log_le_self p hn
    _ = n ^ g.primeFactors.card := Finset.prod_const n

/-- A set of primes below `i` has at most `i / 2` elements: `p ↦ (p - 1) / 2` is injective on
primes and maps those below `i` into `[0, i / 2)`. -/
theorem two_mul_card_le {s : Finset ℕ} {i : ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p < i) :
    2 * s.card ≤ i := by
  have h : s.card ≤ (Finset.range (i / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p - 1) / 2) ?_ ?_
    · intro p hp
      have hp' : p ∈ s := by simpa using hp
      obtain ⟨hpp, hpi⟩ := hs p hp'
      have := hpp.two_le
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro p hp q hq hpq
      have hp' : p ∈ s := by simpa using hp
      have hq' : q ∈ s := by simpa using hq
      obtain ⟨hpp, -⟩ := hs p hp'
      obtain ⟨hqp, -⟩ := hs q hq'
      have h2p := hpp.two_le
      have h2q := hqp.two_le
      have hop := hpp.eq_two_or_odd
      have hoq := hqp.eq_two_or_odd
      simp only at hpq
      omega
  simp only [Finset.card_range] at h
  omega

/-- If no prime `p ≥ i` divides `gcd(C(n, i), C(n, j))`, with `1 ≤ i < j ≤ n / 2`, then
`n ≤ j²`. -/
theorem le_sq_of_counterexample {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n / 2)
    (hcon : ∀ p : ℕ, p.Prime → i ≤ p → ¬ p ∣ Nat.gcd (n.choose i) (n.choose j)) :
    n ≤ j ^ 2 := by
  have hjn' : j ≤ n := le_trans hjn (Nat.div_le_self n 2)
  have hin : i ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hA : 0 < n.choose i := Nat.choose_pos hin
  have hB : 0 < j.choose i := Nat.choose_pos hij.le
  set g := Nat.gcd (n.choose i) (n.choose j) with hg_def
  have hg0 : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ hA).ne'
  -- `C(n, i) ≤ g · C(j, i)`
  have h1 : n.choose i ≤ g * j.choose i :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hg0) hB) (choose_dvd_gcd_mul hij.le)
  -- `g ≤ n ^ c` with `2c ≤ i`, since every prime factor of `g` is below `i`
  have h3 : g ≤ n ^ g.primeFactors.card :=
    le_pow_card_of_dvd_choose hn0 hg0 hin (Nat.gcd_dvd_left _ _)
  have hc : 2 * g.primeFactors.card ≤ i := by
    refine two_mul_card_le (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩)
    by_contra hpi
    exact hcon p (Nat.prime_of_mem_primeFactors hp) (not_lt.1 hpi)
      (Nat.dvd_of_mem_primeFactors hp)
  set c := g.primeFactors.card
  -- `C(j, i) · n^i ≤ C(n, i) · j^i`
  have h2 := choose_mul_pow_le (i := i) hjn'
  have h4 : j.choose i * n ^ i ≤ j.choose i * (n ^ c * j ^ i) :=
    calc j.choose i * n ^ i ≤ n.choose i * j ^ i := h2
      _ ≤ g * j.choose i * j ^ i := Nat.mul_le_mul_right _ h1
      _ ≤ n ^ c * j.choose i * j ^ i := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
      _ = j.choose i * (n ^ c * j ^ i) := by ring
  have h5 : n ^ i ≤ n ^ c * j ^ i := Nat.le_of_mul_le_mul_left h4 hB
  have h6 : n ^ i * n ^ i ≤ n ^ i * (j ^ 2) ^ i :=
    calc n ^ i * n ^ i ≤ (n ^ c * j ^ i) * (n ^ c * j ^ i) := Nat.mul_le_mul h5 h5
      _ = n ^ (2 * c) * (j ^ 2) ^ i := by ring
      _ ≤ n ^ i * (j ^ 2) ^ i := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hnpos hc)
  have h7 : n ^ i ≤ (j ^ 2) ^ i := Nat.le_of_mul_le_mul_left h6 (Nat.pow_pos hnpos)
  exact (Nat.pow_le_pow_iff_left (by omega)).1 h7

/-- Erdős Problem 699 holds whenever `j² < n`. -/
theorem of_sq_lt :
    ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 → j ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  intro n i j hi hij hjn hsq
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have := le_sq_of_counterexample hi hij hjn hcon
  omega

end Erdos699
