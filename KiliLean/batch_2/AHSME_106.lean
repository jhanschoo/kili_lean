import Mathlib

/- For each nonnegative integer $n$, let
$a_n = \frac{(n+10)!}{n!}$
Let $k$ denote the smallest nonnegative integer for which the rightmost nonzero digit of $a_k$ is odd. The rightmost nonzero digit of $a_k$ is

$\mathrm{(A) \ }1 \qquad \mathrm{(B) \ }3 \qquad \mathrm{(C) \ }5 \qquad \mathrm{(D) \ } 7 \qquad \mathrm{(E) \ } 9$ -/
theorem AHSME_106 (Q : ℕ → Prop) (a : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ n, Q n ↔ ∃ p t, a n = p * 10 ^ t ∧ (p % 10) % 2 = 1)
    (ha : ∀ n, a n = (n + 10).factorial / n.factorial)
    (hk : IsLeast { k' : ℕ | Q k' } k) :
    ∃ p t, a k = p * 10 ^ t ∧ p % 10 = 9 := by
  have prime_factorization (n : ℕ) (npos : n ≠ 0) : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
    calc
      n = id n := rfl
      _ = n.factorization.prod fun (p k : ℕ) => id (p ^ k) := by
        rw [Nat.multiplicative_factorization id (by intro x y _; simp only [id_eq]) (by simp only [id_eq]) npos]
      _ = n.factorization.prod fun (p k : ℕ) => (p ^ k) := by simp
      _ = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
        rw [Nat.prod_factorization_eq_prod_primeFactors]
  -- We have $a_n = n(n+1)\dots (n+9)$.
  have apos n : a n ≠ 0 := by
    rw [ha n, ← Nat.ascFactorial_eq_div]
    positivity
  replace ha n : a n = ∏ i ∈ Finset.range 10, (n + 1 + i) := by
    rw [← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_div, ha]
  have ha2 n : ∃ x r, ¬ 2 ∣ r ∧ a n = 2 ^ x * r :=
    WfDvdMonoid.max_power_factor (apos n) <| (Nat.irreducible_iff_nat_prime _).mpr (Nat.prime_two)
  have ha5 n : ∃ x r, ¬ 5 ∣ r ∧ a n = 5 ^ x * r :=
    WfDvdMonoid.max_power_factor (apos n) <| (Nat.irreducible_iff_nat_prime _).mpr (Nat.prime_five)
  have hxy n (hQn : Q n) : x n ≤ y n := by
    rw [hQ] at hQn
    obtain ⟨p, t, ⟨hp, hodd⟩⟩ := hQn
    simp [hx, hy]
    by_contra!
