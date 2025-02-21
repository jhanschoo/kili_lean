import Mathlib

/--
PROBLEM:
If $a < b < c < d < e $ are [consecutive](https://artofproblemsolving.com/wiki/index.php/Consecutive) [positive](https://artofproblemsolving.com/wiki/index.php/Positive) [integers](https://artofproblemsolving.com/wiki/index.php/Integer) such that $b+c+d$ is a [perfect square](https://artofproblemsolving.com/wiki/index.php/Perfect_square) and $a+b+c+d+e$ is a [perfect cube](https://artofproblemsolving.com/wiki/index.php/Perfect_cube), what is the smallest possible value of $c$?
-/
theorem number_theory_701
  (P : ℤ → Prop)
  (hP : ∀ (c : ℤ), P c = (
    ∃ (a b d e t u : ℤ), 0 < a ∧ a + 1 = b ∧ b + 1 = c ∧ c + 1 = d ∧ d + 1 = e ∧
      t ^ 2 = b + c + d ∧
      u ^ 3 = a + b + c + d + e))
  : (∀ c, P c → 675 ≤ c) ∧ P 675 := by
  -- First, note that if $d$ divides $a$, then $d^n$ divides $a^n$ for any positive integer $n$.
  have : ∀ (a d : ℤ) n, d ∣ a → d ^ n ∣ a ^ n := by
    intros a d n hd
    exact pow_dvd_pow_of_dvd hd n
  -- Also, notice that if $c$ is the middle of an odd number of consecutive positive integers, then the sum of the integers is the middle integer times the number of integers. In particular, $b + c + d = 3c$ and $a + b + c + d + e = 5c$.
  have : ∀ (a : ℤ), a + 1 + (a + 2) + (a + 3) = 3 * (a + 2) := by
    intro a; ring
  have : ∀ (a : ℤ), a + (a + 1) + (a + 2) + (a + 3) + (a + 4) = 5 * (a + 2) := by
    intro a; ring
  constructor
  -- Hence consider a list of five consecutive positive integers.
  · intro c hPc
    rw [hP] at hPc
    rcases hPc with ⟨a, b, d, e, t, u, ⟨hpos, hab, hbc, hcd, hde, hsq, hcu⟩⟩
    -- We know that $b + c + d = 3c$ and $a + b + c + d + e = 5c$.
    have hsq' : 3 * c = t ^ 2 := by linarith
    have hcu' : 5 * c = u ^ 3 := by linarith
    have h3p : Prime (3 : ℤ) := by exact Int.prime_three
    have h5p : Prime (5 : ℤ) := by rw [Int.prime_iff_natAbs_prime]; norm_num
    -- Since $b + c + d = 3c$ is the perfect square of $t$, then $t^2$ is a multiple of $3$. But since $3$ is prime, $t$ is a multiple of $3$. So $3c$ is a multiple of $3^2$, so $c$ is a multiple of $3$.
    have ht3 : 3 ∣ t := by
      have : 3 ∣ t ^ 2 := by exact Dvd.intro c hsq'
      exact Prime.dvd_of_dvd_pow h3p this
    have ht3' : 3 ^ 2 ∣ 3 * c := by
      rw [hsq']
      exact pow_dvd_pow_of_dvd ht3 2
    have ht3'' : 3 ∣ c := by
      rw [pow_two] at ht3'
      have : (3 : ℤ) ≠ 0 := by norm_num
      exact (mul_dvd_mul_iff_left this).mp ht3'
    -- Next, since $a + b + c + d + e = 5c$ is the perfect cube of $u$, then $u^3$ is a multiple of $5$. But since $5$ is prime, $5$ is a multiple of $u$ as well. Moreover, since $c$ is a multiple of $3$, so also is $u^3=5c$. The same argument as before shows that $u$ is a multiple of $3$.
    have hu5 : 5 ∣ u := by
      have : 5 ∣ u ^ 3 := by exact Dvd.intro c hcu'
      exact Prime.dvd_of_dvd_pow h5p this
    have hu3 : 3 ∣ u := by
      have : 3 ∣ u ^ 3 := by
        rw [← hcu']
        exact Dvd.dvd.mul_left ht3'' 5
      exact Prime.dvd_of_dvd_pow h3p this
    -- Since $u$ is a multiple of $3$ and $5$, both of them prime, $u$ is a multiple of $3 \times 5 = 15$.
    have hu15 : 5 * 3 ∣ u := by
      apply IsCoprime.mul_dvd (by norm_num) hu3 hu5
    -- Then $5c$ must be a multiple of the cube of $15$.
    have hu15' : (5 * 3) ^ 3 ∣ 5 * c := by
      rw [hcu']
      exact pow_dvd_pow_of_dvd hu15 3
    -- In particular, $c$ is a multiple of $3^3 \cdot 5^2$.
    have hdiv : 3 ^ 3 * 5 ^ 2 ∣ c := by
      have : ((5 : ℤ) * 3) ^ 3 = 5 * (3 ^ 3 * 5 ^ 2) := by ring
      rw [this] at hu15'
      have : (5 : ℤ) ≠ 0 := by norm_num
      exact (mul_dvd_mul_iff_left this).mp hu15'
    -- The smallest such number is $3^3 \cdot 5^2 = 675$.
    simp at hdiv
    exact Int.le_of_dvd (by linarith) hdiv
  · -- Finally, we check that $75$ satisfies the property.
    rw [hP]
    use 673, 674, 676, 677, 45, 15
    constructor <;> simp
