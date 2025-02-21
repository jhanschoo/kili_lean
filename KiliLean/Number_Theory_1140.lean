import Mathlib

/--
PROBLEM:
For how many positive integers $m$ is
\[\frac{2002}{m^2 -2}\]
a positive integer?
-/
theorem number_theory_1140 (n : ℕ) (S : Finset ℕ) (hn : n = S.card) (hS : ∀ (m : ℕ), m ∈ S ↔ (m > 0 ∧ (m ^ 2 - 2 > 0) ∧ ∃ k > 0, 2002 = (m ^ 2 - 2) * k)) : n = 3 := by
  -- Again, memorizing the prime factorization of $2002$ is helpful. $2002 = 2 \cdot 7 \cdot 11 \cdot 13$,
  have hpf : (2002).primeFactorsList = [2, 7, 11, 13] := by
    simp [Nat.primeFactorsList, Nat.minFac, Nat.minFacAux, Nat.dvd_iff_mod_eq_zero, -Nat.toFinset_factors]
  -- so its factors are $1, 2, 7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001,$ and $1002$.
