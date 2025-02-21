import Mathlib

/--
PROBLEM:
Let $x$ and $y$ be positive integers such that $7x^5 = 11y^{13}.$ The minimum possible value of $x$ has a prime factorization $a^cb^d.$ What is $a + b + c + d?$
-/
theorem number_theory_1145 (P : ℕ → Prop ) (Q : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) (hP : ∀ x, P x ↔ x > 0 ∧ ∃ y > 0, 7 * x ^ 5 = 11 * y ^ 13) (hQ : ∀ x a b c d, Q x a b c d ↔ Nat.Prime a ∧ Nat.Prime b ∧ a < b ∧ c > 0 ∧ d > 0 ∧ IsLeast { x : ℕ | P x } x ∧ x = a ^ c * b ^ d) (_hhint : ∃ x a b c d, Q x a b c d) : ∃ x a b c d, Q x a b c d ∧ a + b + c + d = 31 := by
  -- Let x
  have hPx : ∀ x y, P x → 7 * x ^ 5 = 11 * y ^ 13 → 5 ≤ (x).factorization 7 ∧ 8 ≤ (x).factorization 11 := by
    intro x y hPx hxy
    rw [hP] at hPx
    rcases hPx with ⟨_hxpos, ⟨y', hypos, hxy'⟩⟩
    have : y = y' := by
      have : 11 * y ^ 13 = 11 * y' ^ 13 := by rw [← hxy, hxy']
      have hpos11 : 11 > 0 := by norm_num
      have : y ^ 13 = y' ^ 13 := Nat.eq_of_mul_eq_mul_left hpos11 this
      -- by aesop
      simp_all only [gt_iff_lt, Nat.ofNat_pos, zero_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj, pow_pos]
    subst this
    clear hxy'
    -- From the equation, it follows that the minimum value of $x$ must involve factors of $7$ and $11$.
    have hp7 : Nat.Prime 7 := by norm_num
    have hp11 : Nat.Prime 11 := by norm_num
    -- Thus, we try to look for the lowest power $p$ of $11$ such that $13p + 1 \equiv 0 \pmod{5}$, so that we can take $11^{13p + 1}$ to the fifth root. Similarly, we want to look for the lowest power $n$ of $7$ such that $13n - 1 \equiv 0 \pmod{5}$.
    set c := (x).factorization 7
    set d := (x).factorization 11
    set n := (y).factorization 7 with hn
    set p := (y).factorization 11 with hp

    have hy13pos : y ^ 13 > 0 := pow_pos hypos _
    have dvd5p' : 5 * d = 1 + 13 * p := by
      calc
        5 * d = (x ^ 5).factorization 11 := by simp [hp11]
        _ = (7 * x ^ 5).factorization 11 := by rw [Nat.factorization_mul (by linarith) (by linarith)]; simp [hp7]
        _ = (11 * y ^ 13).factorization 11 := by rw [hxy]
        _ = 1 + 13 * p := by
          rw [Nat.factorization_mul (by linarith) (by linarith)]; simp [hp11]
    have hplb : 3 ≤ p := by
      have dvd5p : 5 ∣ 1 + 13 * p := Dvd.intro d dvd5p'
      by_contra contra
      simp at contra
      interval_cases p <;> norm_num at dvd5p
    have dvd5n' : 1 + 5 * c = 13 * n := by
      calc
        1 + 5 * c = (7 * x ^ 5).factorization 7 := by rw [Nat.factorization_mul (by linarith) (by linarith)]; simp [hp7]
        _ = (11 * y ^ 13).factorization 7 := by rw [hxy]
        _ = 13 * n := by rw [Nat.factorization_mul (by linarith) (by linarith)]; simp [hp11]
    have hnlb : 2 ≤ n := by
      by_contra contra
      simp at contra
      interval_cases n
      · norm_num at dvd5n'
      · have : 5 * c = 12 := by linarith
        have : 5 ∣ 12 := Dvd.intro c this
        norm_num at this
    have hclb : 5 ≤ c := by linarith
    have hdlb : 8 ≤ d := by linarith
    exact ⟨hclb, hdlb⟩
  -- when the inequalities on $p$ and $n$ are equalities $p = 3$ and $n = 2$, we have $c = 5$ and $d = 8$. We verify that this is a possible value of $x$, and by the above reasoning, it is the smallest possible value of $x$.
  use (7 ^ 5) * (11 ^ 8), 7, 11, 5, 8
  rw [hQ]
  constructor
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · constructor
    · simp only [Set.mem_setOf_eq]
      rw [hP]
      constructor
      · norm_num
      use 7 ^ 2 * 11 ^ 3
      constructor
      · norm_num
      ring
    · simp only [lowerBounds, Set.mem_setOf_eq]
      intro x hx
      have hx' := hx
      rw [hP] at hx'
      rcases hx' with ⟨hxpos, ⟨y, _hypos, hxy⟩⟩
      rcases (hPx x y hx hxy) with ⟨h7, h11⟩
      apply Nat.le_of_dvd hxpos
      have h75dvd : 7 ^ 5 ∣ x := Nat.dvd_trans (pow_dvd_pow _ h7) (Nat.ord_proj_dvd _ _)
      have h118dvd : 11 ^ 8 ∣ x := Nat.dvd_trans (pow_dvd_pow _ h11) (Nat.ord_proj_dvd _ _)
      have h75118cop : (7 ^ 5).Coprime (11 ^ 8) := by norm_num
      rw [← Nat.Coprime.lcm_eq_mul h75118cop]
      exact lcm_dvd h75dvd h118dvd
  · rfl
  · norm_num
