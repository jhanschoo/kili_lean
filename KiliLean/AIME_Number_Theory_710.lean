import Mathlib

/--
PROBLEM:
Find the least positive integer $n$ such that no matter how $10^{n}$ is expressed as the product of any two positive integers, at least one of these two integers contains the digit $0$.
-/
theorem AIME_Number_Theory_710 (P Q : ℕ → Prop) (hQ : ∀ n, Q n = ∃ b, 0 < n / 10 ^ b ∧ n / 10 ^ b % 10 = 0) (hP : ∀ n, P n = ∀ a b, a ≤ b → a * b = 10 ^ n → Q a ∨ Q b) : IsLeast { n : ℕ | 0 < n ∧ P n } 8 := by
  -- If a factor of $10^{n}$ has a $2$ and a $5$ in its prime factorization, then that factor will end in a $0$.
  have hfact10 (n : ℕ) : 10 ^ n = 2 ^ n * 5 ^ n := by rw [← mul_pow]; simp
  have hNotPPow : ∀ n d, d ∣ 10 ^ n → 10 ∣ d → Q d := by
    intros n d hd h10
    rw [hQ]
    use 0
    simp
    constructor
    · exact Nat.pos_of_dvd_of_pos hd (by positivity)
    · omega
  -- Therefore, we have left to consider the case when the two factors have the $2$s and the $5$s separated, so we need to find the first power of 2 or 5 that contains a 0.
  have hExQ : ∀ n a b, 0 < n → a ≤ b → a * b = 10 ^ n → ¬ Q a → ¬ Q b → a = 2 ^ n ∧ b = 5 ^ n := by
    intros n a b hnpos haleb hab ha hb
    by_cases h2a : 2 ∣ a
    · by_cases h5a : 5 ∣ a
      · have ha1 : a ∣ 10 ^ n := Dvd.intro b hab
        have ha2 : 2 * 5 ∣ a := Nat.Prime.dvd_mul_of_dvd_ne (by norm_num) (by norm_num) (by norm_num) h2a h5a
        simp at ha2
        specialize hNotPPow n a ha1 ha2
        contradiction
      · have h5nab : 5 ^ n ∣ a * b := by
          rw [hab, hfact10]
          rw [Nat.Coprime.dvd_mul_left]
          exact Nat.coprime_pow_primes _ _ (by norm_num) (by norm_num) (by norm_num)
        have h5nb : 5 ^ n ∣ b := by
          rwa [Nat.Coprime.dvd_mul_left] at h5nab
          apply Nat.Coprime.pow_left
          rwa [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
        have h5b : 5 ∣ b := Nat.dvd_of_pow_dvd (by linarith : 1 ≤ n) h5nb
        by_cases h2b : 2 ∣ b
        · have h10b : 2 * 5 ∣ b := Nat.Prime.dvd_mul_of_dvd_ne (by norm_num) (by norm_num) (by norm_num) h2b h5b
          simp at h10b
          specialize hNotPPow n b (Dvd.intro_left a hab) h10b
          contradiction
        · have h5b : b = 5 ^ n := by
            apply Nat.dvd_antisymm _ h5nb
            have := Dvd.intro_left a hab
            rw [hfact10] at this
            rwa [Nat.Coprime.dvd_mul_left] at this
            apply Nat.Coprime.pow_right
            apply Nat.Coprime.symm
            rwa [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
          rw [hfact10] at hab
          rw [h5b] at hab
          apply mul_right_cancel₀ (by norm_num) at hab
          tauto
    · have h2nab : 2 ^ n ∣ a * b := by
        rw [hab, hfact10, Nat.Coprime.dvd_mul_right]
        exact Nat.coprime_pow_primes _ _ (by norm_num) (by norm_num) (by norm_num)
      have h2nb : 2 ^ n ∣ b := by
        rwa [Nat.Coprime.dvd_mul_left] at h2nab
        apply Nat.Coprime.pow_left
        rwa [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
      have h2b : 2 ∣ b := Nat.dvd_of_pow_dvd (by linarith : 1 ≤ n) h2nb
      by_cases h5b : 5 ∣ b
      · have h10b : 2 * 5 ∣ b := Nat.Prime.dvd_mul_of_dvd_ne (by norm_num) (by norm_num) (by norm_num) h2b h5b
        simp at h10b
        specialize hNotPPow n b (Dvd.intro_left a hab) h10b
        contradiction
      · have h2b : b = 2 ^ n := by
          apply Nat.dvd_antisymm _ h2nb
          have := Dvd.intro_left a hab
          rw [hfact10] at this
          rwa [Nat.Coprime.dvd_mul_right] at this
          apply Nat.Coprime.pow_right
          apply Nat.Coprime.symm
          rwa [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
        rw [hfact10, h2b, mul_comm] at hab
        apply mul_left_cancel₀ (by norm_num) at hab
        subst a
        subst b
        apply le_of_pow_le_pow_left₀ (by positivity) (by positivity) at haleb
        linarith
  simp [IsLeast, hP, -Nat.reducePow]
  constructor
  swap
  · simp [lowerBounds]
    intro n hn hPn
    by_contra! hle
    specialize hPn (2 ^ n) (5 ^ n) (by apply Nat.pow_le_pow_of_le_left (by norm_num)) (by rw [← mul_pow]; simp)
    rw [hQ, hQ] at hPn
    have hQ' : ∀ d i b, d < 10 → i ≠ 0 → 0 < d ^ i / 10 ^ b → b < i := by
      intros d i b hd hipos hi
      by_contra! hib
      have : 10 ^ b = 0 ∨ d ^ i < 10 ^ b := by
        right
        calc
          d ^ i < 10 ^ i := Nat.pow_lt_pow_left hd hipos
          _ ≤ 10 ^ b := Nat.pow_le_pow_of_le_right (by linarith) hib
      rw [← Nat.div_eq_zero_iff] at this
      linarith
    -- For $n = 1$, $2^1 = 2 , 5^1 = 5$, $n = 2$, $2^2 = 4 , 5 ^ 2 =25$, $n = 3$, $2^3 = 8 , 5 ^3 = 125$, and so on,
    interval_cases n
      <;> rcases hPn with (⟨b, hbl, hbr⟩ | ⟨b, hbl, hbr⟩)
      <;> have hbub := hQ' _ _ _ (by norm_num) (by norm_num) hbl
      <;> interval_cases b
      <;> simp at hbl hbr
  · -- until, $n = 8:$ $2^8 = 256$ | $5^8 = 390625$
    intro a b haleb hab
    specialize hExQ 8 a b (by positivity) haleb hab
    by_cases hab' : a = 2 ^ 8 ∧ b = 5 ^ 8
    · rcases hab' with ⟨rfl, rfl⟩
      simp
      right
      rw [hQ]
      use 3
      simp
    · tauto
