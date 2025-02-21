import Mathlib

/--
Let $m/n$, in lowest terms, be the [probability](https://artofproblemsolving.com/wiki/index.php/Probability) that a randomly chosen positive [divisor](https://artofproblemsolving.com/wiki/index.php/Divisor) of $10^{99}$ is an integer multiple of $10^{88}$. Find $m + n$.
-/
theorem number_theory_698 (p : ℚ) : p = (mkRat {d ∈ Nat.divisors (10 ^ 99) | 10 ^ 88 ∣ d}.card (Nat.divisors (10 ^ 99)).card) → p.num + p.den = 634 := by
  -- $10^n has prime factors $2$ and $5$.
  have h10pf (n : ℕ) (hnpos : 0 < n) : (10 ^ n).primeFactors = {2, 5} := by
    rw [Nat.primeFactors_pow _ (by positivity), Nat.primeFactors_mul (by positivity : 2 ≠ 0) (by positivity : 5 ≠ 0), Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num), Finset.insert_eq]
  -- More precisely, $10^n = 2^n 5^n$
  have h10fact (n : ℕ) (hnpos : 0 < n) :=
    calc
      (10 ^ n).factorization = (2 ^ n * 5 ^ n).factorization := by congr; rw [← mul_pow]; simp
      _ = (2 ^ n).factorization + (5 ^ n).factorization := by rw [Nat.factorization_mul (by positivity) (by positivity)]
      _ = (fun₀ | 2 => n) + fun₀ | 5 => n := by rw [Nat.Prime.factorization_pow (by decide), Nat.Prime.factorization_pow (by decide)]
  -- so it has $(n + 1)(n + 1)$ factors.
  have h10dcard (n : ℕ) (hnpos : 0 < n) :=
    calc
      (Nat.divisors (10 ^ n)).card
        = ∏ x ∈ (10 ^ n).primeFactors, ((10 ^ n).factorization x + 1) := Nat.card_divisors (by positivity)
      _ = ∏ x ∈ {2, 5}, ((10 ^ n).factorization x + 1) := by rw [h10pf n hnpos]
      _ = ((10 ^ n).factorization 2 + 1) * ((10 ^ n).factorization 5 + 1) := by norm_num
      _ = (n + 1) * (n + 1) := by rw [h10fact n hnpos]; simp
  -- Out of $(99 + 1)(99 + 1)$, we only want those factors of $10^{99}$ which are divisible by $10^{88}$; it is easy to draw a [bijection](https://artofproblemsolving.com/wiki/index.php/Bijection) to the number of factors that $10^{11} = 2^{11}5^{11}$ has, which is $(11 + 1)(11 + 1) = 144$
  set mul1088 : ℕ ↪ ℕ := ⟨fun n ↦ 10 ^ 88 * n, by intro n n'; simp⟩
  have numset : {d ∈ Nat.divisors (10 ^ 99) | 10 ^ 88 ∣ d} = Finset.map mul1088 (10 ^ 11).divisors := by
    rw [← Nat.filter_dvd_eq_divisors (by decide)]
    have : 10 ^ 99 = 10 ^ 88 * 10 ^ 11 := by ring
    rw [this]
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Nat.mem_divisors, mul1088]
    constructor
    · intro ⟨⟨hdub, hd99⟩, ⟨k, hk⟩⟩
      subst d
      use k
      simp [-Nat.reducePow]
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) hd99
    · intro ⟨k, ⟨⟨hkd11, _hkpos⟩, hkmap⟩⟩
      subst d
      simp [-Nat.reducePow]
      have := mul_dvd_mul (dvd_refl (10 ^ 88)) hkd11
      constructor
      · rw [Nat.lt_succ_iff]
        exact Nat.le_of_dvd (by positivity) this
      · exact this
  -- Our probability is $\frac{m}{n} = \frac{144}{10000} = \frac{9}{625}$
  rw [numset, Finset.card_map, h10dcard 11 (by positivity), h10dcard 99 (by positivity)]
  intro hp
  have hpnd : p.num = 9 ∧ p.den = 625 := by
    rw [hp]
    simp [mkRat, Rat.normalize]
    rfl
  -- So $m + n = 9 + 625 = 634$
  linarith
