import Mathlib

/--
PROBLEM:PROBLEM:
Maya lists all the positive divisors of $2010^2$. She then randomly selects two distinct divisors from this list. Let $p$ be the [probability](https://artofproblemsolving.com/wiki/index.php/Probability) that exactly one of the selected divisors is a [perfect square](https://artofproblemsolving.com/wiki/index.php/Perfect_square). The probability $p$ can be expressed in the form $\frac {m}{n}$, where $m$ and $n$ are [relatively prime](https://artofproblemsolving.com/wiki/index.php/Relatively_prime) positive integers. Find $m + n$.
-/
theorem number_theory_739 (Psq : ℕ → Prop) (hPsq : ∀ n, Psq n = ∃ r, r ^ 2 = n) (P : ℤ → Prop) (hP : ∀ (ans : ℤ), P ans = ∃ (p : ℚ), ∀ (s t : Finset (ℕ × ℕ)) (x : ℕ × ℕ), p = (s.card : ℚ) / (t.card : ℚ) ∧ (x ∈ t ↔ (x.1 ∣ 2010 ^ 2 ∧ x.2 ∣ 2010 ^ 2)) ∧ (x ∈ s ↔ (x ∈ t ∧ Psq x.1 ↔ ¬Psq x.2)) ∧ ans = p.num + p.den) : (∀ z, P z → z = 107) ∧ P 107 := by
  have hpf : (2010 ^ 2).primeFactorsList = [2, 2, 3, 3, 5, 5, 67, 67] := by
    simp [Nat.primeFactorsList, Nat.minFac, Nat.minFacAux, Nat.dvd_iff_mod_eq_zero, -Nat.toFinset_factors]
  rw [hP]
  constructor
  · sorry
  · use { num := 26, den := 81 }
    simp [hpf, hPsq]
    ring
