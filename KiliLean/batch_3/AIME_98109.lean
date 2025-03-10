import Mathlib

set_option maxRecDepth 1000

/- The decimal representation of $m/n,$ where $m$ and $n$ are relatively prime positive integers and $m < n,$ contains the digits $2, 5$, and $1$ consecutively and in that order. Find the smallest value of $n$ for which this is possible. -/
theorem number_theory_98109 :
IsLeast {x | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m < n ∧ Nat.Coprime m n ∧ x = n ∧ ∃ b, ⌊10 ^ b * (m / n : ℚ)⌋₊ % 1000 = 251} 127 := by
  simp [IsLeast, lowerBounds]
  constructor
  · -- the property is satisfied with m = 32, n = 127, and b = 3
    refine ⟨32, ?_, 127, ?_, ?_, ?_, rfl, 3, ?_⟩
    any_goals norm_num
    rw [
      ((Nat.floor_eq_iff (by positivity)).mpr ⟨by norm_num, by norm_num⟩ : ⌊(32000 : ℚ) / 127⌋₊ = 251)
    ]
  · -- we now show that n = 127 is the least such n
    intro n m mpos n' npos hmn1 hmn2 hnn' b heq
    subst hnn'
    have mnpos : 0 < (m : ℚ) / n := by positivity
    have mnle1 : (m : ℚ) / n < 1 := by
      rw [div_lt_one (by norm_cast)]
      norm_cast
    set mn10b := 10 ^ b * ((m : ℚ) / n) with hmn10b
    have mn10bpos : 0 < mn10b := by positivity
    have hblb : 3 ≤ b := by
      by_contra! hb
      replace hb := Nat.le_of_lt_succ hb
      have : mn10b ≤ 100 := calc
        mn10b = 10 ^ b * ((m : ℚ) / n) := hmn10b
        _ ≤ 10 ^ b * 1 := by rel [mnle1]
        _ = 10 ^ b := mul_one _
        _ ≤ 10 ^ 2 := pow_le_pow_right₀ (by norm_num) hb
        _ = 100 := by norm_num
      have : ⌊mn10b⌋₊ ≤ 100 := by
        qify
        exact (le_trans (Nat.floor_le (by positivity)) this)
      have : 251 < 251 := calc
        251 = ⌊mn10b⌋₊ % 1000 := heq.symm
        _ = ⌊mn10b⌋₊ := Nat.mod_eq_of_lt (lt_of_le_of_lt this (by norm_num))
        _ ≤ 100 := this
        _ < 251 := by norm_num
      contradiction
    -- In fact, it suffices that b = 3; we first do some preliminary work
    -- We extract X out as the integer formed by the first (b - 3) digits of m / n
    set X := ⌊10 ^ (b-3) * ((m : ℚ) / n)⌋₊ with hX
    have hXfle : ⌊10 ^ (b-3) * ((m : ℚ) / n)⌋₊ ≤ 10 ^ (b-3) * ((m : ℚ) / n) := Nat.floor_le (by positivity)
    have hmXr : mn10b = X * 10 ^ 3 + (mn10b - X * 10 ^ 3) := by ring
    -- Then in fact m10b - X = m10b % 1000
    have hr1 : mn10b - X * 10 ^ 3 = mn10b - (⌊mn10b⌋₊ / 1000 * 1000 : ℕ) := calc
      mn10b - X * 10 ^ 3 = mn10b - (⌊10 ^ (b - 3) * ((m : ℚ) / n)⌋₊ * 10 ^ 3 : ℕ) := by
        rw [hX]
        norm_cast
      _ = mn10b - (⌊mn10b⌋₊ / 1000 * 1000 : ℕ) := by
        congr
        rw [hmn10b, pow_sub₀ 10 (by norm_num) hblb, mul_assoc, mul_comm ((10 ^ 3)⁻¹) _, ← mul_assoc, ← div_eq_mul_inv, (by norm_cast : (10 ^ 3 : ℚ) = ((10 ^ 3 : ℕ):ℚ)), Nat.floor_div_nat]
        norm_num
    have hr2 : ⌊mn10b - X * 10 ^ 3⌋₊ = 251 := calc
      ⌊mn10b - X * 10 ^ 3⌋₊ = ⌊mn10b - (⌊mn10b⌋₊ / 1000 * 1000 : ℕ)⌋₊ := by
        rw [hr1]
      _ = ⌊mn10b⌋₊ - ⌊mn10b⌋₊ / 1000 * 1000 := Nat.floor_sub_nat _ _
      _ = ⌊mn10b⌋₊ % 1000 := by
        apply Nat.sub_eq_of_eq_add
        rw [add_comm, Nat.div_add_mod']
      _ = 251 := heq
    have hnXle : n * X ≤ 10 ^ (b - 3) * m := by
      rw [hX]
      qify
      calc
        n * (⌊10 ^ (b - 3) * ((m : ℚ) / n)⌋₊:ℚ) ≤ n * 10 ^ (b - 3) * ((m : ℚ) / n) := by
          rw [mul_assoc (n:ℚ) _ ((m:ℚ)/n)]
          apply (mul_le_mul_left (by positivity)).mpr hXfle
        _ = 10 ^ (b - 3) * m := by
          ring_nf
          rw [mul_comm (n : ℚ) (m : ℚ), mul_assoc (m : ℚ) _ _, mul_inv_cancel₀ (by positivity), mul_one]
    have hnXlt : n * X < 10 ^ (b - 3) * m := by
      apply Nat.lt_of_sub_ne_zero
      have : (⌊mn10b - (X:ℚ) * 10 ^ 3⌋₊:ℚ) = 251 := by
        norm_cast
        rw [← hr2]
        congr
        norm_cast
      have : 251 ≤ mn10b - X * 10 ^ 3 := by
        rw [← this]
        apply Nat.floor_le
        rw [hr1]
        rw [le_sub_iff_add_le', add_zero]
        apply le_trans (by norm_cast; exact Nat.div_mul_le_self _ _) (Nat.floor_le (by positivity))
      have : n * 251 ≤ (10 ^ (b - 3) * (m:ℚ) - n * X) * 10 ^ 3 := calc
        n * 251 ≤ n * (mn10b - X * 10 ^ 3) := by rel [this]
        _ = n * mn10b - n * X * 10 ^ 3 := by ring
        _ = n * (10 ^ b * ((m : ℚ) / n)) - n * X * 10 ^ 3 := by rw [hmn10b]
        _ = 10 ^ b * ((m : ℚ) / n * n) - n * X * 10 ^ 3 := by ring
        _ = 10 ^ b * (m : ℚ) - n * X * 10 ^ 3 := by rw [div_mul_cancel₀ _ (by positivity)]
        _ = 10 ^ (b - 3) * (m:ℚ) * 10 ^ 3 - n * X * 10 ^ 3 := by
          congr 1
          rw [mul_assoc, mul_comm (m : ℚ), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hblb]
        _ = (10 ^ (b - 3) * (m:ℚ) - n * X) * 10 ^ 3 := by rw [mul_sub_right_distrib _ _ _]
      have : (10 ^ (b - 3) * m - n * X) * 1000 ≠ 0 := by
        qify
        rw [Nat.cast_sub hnXle]
        norm_cast at this ⊢
        rw [(by norm_num : 1000 = 10 ^ 3)]
        intro contra
        rw [contra, Nat.le_zero, Nat.mul_eq_zero] at this
        rcases this with this | this
        · subst n; contradiction
        · contradiction
      exact Nat.ne_zero_of_mul_ne_zero_left this
    -- We can do some algebraic manipulation to write mn10b / 10 ^ 3 - X as m' / n', with m, n positive integers
    have hr1' : ((10 ^ (b - 3) * m - n * X : ℕ) : ℚ) / n = mn10b / 10 ^ 3 - X := by
      apply mul_right_cancel₀ (by positivity: (n : ℚ) ≠ 0)
      rw [div_mul_cancel₀ _ (by positivity), hmn10b]
      calc
        ((10 ^ (b - 3) * m - n * X : ℕ) : ℚ) = (10 ^ (b - 3) * (m : ℚ) - n * X) := by
          rw [Nat.cast_sub hnXle]; norm_cast
        _ = (10 ^ b * (10 ^ 3)⁻¹ * ((m : ℚ) / n * n) - n * X) := by
          rw [pow_sub₀ _ (by norm_num) hblb, div_mul_cancel₀ _ (by positivity)]
        _ = (10 ^ b * ((m : ℚ) / n) / 10 ^ 3 - X) * n := by ring
        _ = (mn10b / 10 ^ 3 - ↑X) * n := by rw [hmn10b]
    set m' := (10 ^ (b - 3) * m - n * X : ℕ) with hm'
    -- Except for coprimality which is easily recovered by quotienting against the gcd,
    -- we have shown that the hypotheses hold for m' and n and now prove the problem with respect to them
    have m'pos : 0 < m' := by
      rw [hm']
      exact Nat.lt_sub_of_add_lt (by linarith)
    have hm'lem : m' < n := by
      rw [hm', hX]
      qify
      rw [← div_lt_one (by positivity)]
      calc
        ((10 ^ (b - 3) * m - n * ⌊10 ^ (b - 3) * ((m :ℚ) / n)⌋₊:ℕ):ℚ) / n
          = (10 ^ (b - 3) * m - n * (⌊10 ^ (b - 3) * ((m :ℚ) / n)⌋₊:ℚ)) / n := by
          rw [Nat.cast_sub hnXle]
          qify
        _ = 10 ^ (b - 3) * (m / n) - (n / n) * (⌊10 ^ (b - 3) * ((m :ℚ) / n)⌋₊:ℚ) := by ring
        _ = 10 ^ (b - 3) * (m / n) - (⌊10 ^ (b - 3) * ((m :ℚ) / n)⌋₊:ℚ) := by
          rw [div_self (by positivity), one_mul]
        _ < 1 := by
          rw [sub_lt_iff_lt_add', ← sub_lt_iff_lt_add]
          exact Nat.sub_one_lt_floor (10 ^ (b - 3) * ((m:ℚ) / n))
    have hm'nle1 : (m':ℚ) / n < 1 := by
      rw [div_lt_one]
      norm_cast
      positivity
    have heq' : ⌊1000 * ((m':ℚ) / n)⌋₊ = 251 := calc
      ⌊1000 * ((m':ℚ) / n)⌋₊ = ⌊((10 ^ (b - 3) * 10 ^ 3) * ((m:ℚ) / n) - 10 ^ 3 * (n / n) * X)⌋₊ := by
        rw [hm', Nat.cast_sub hnXle]
        norm_num
        ring_nf
      _ = ⌊mn10b - X * 10 ^ 3⌋₊ := by
        rw [← pow_add, Nat.sub_add_cancel hblb, div_self (by positivity), mul_one, hmn10b, mul_comm (X:ℚ)]
      _ = 251 := by
        rw [hr2]
    -- from the floor operation we obtain the following bounds:
    -- note that we maintain these bounds in ℚ for technical ease
    have heq'l : 251 * (n:ℚ) ≤ 1000 * m' := by
      qify at heq'
      rw [← (le_div_iff₀ (by positivity)), mul_div_assoc, ← heq']
      exact Nat.floor_le (by positivity)
    have heq'l' : n ≤ 250 * (4 * (m':ℚ) - n) := calc
      (n:ℚ) = 251 * (n:ℚ) - 250 * n := by ring
      _ ≤ 1000 * (m':ℚ) - 250 * n := by rel [heq'l]
      _ = 250 * (4 * (m':ℚ) - n) := by ring
    have heq'u : 1000 * (m':ℚ) < 252 * n := by
      qify at heq'
      rw [← (div_lt_iff₀ (by positivity)), mul_div_assoc, (by norm_num : (252:ℚ) = 251 + 1), ← heq']
      exact Nat.lt_floor_add_one _
    have heq'u' : 250 * (4 * (m':ℚ) - n) < 2 * n := calc
      250 * (4 * (m':ℚ) - n) = (1000 * (m':ℚ)) - 250 * n := by ring
      _ < (252 * (n:ℚ)) - 250 * n := by rel [heq'u]
      _ = 2 * (n:ℚ) := by ring
    have h4m'npos : 0 < 4 * (m':ℚ) - n := by
      refine pos_of_mul_pos_right ?_ (by norm_num : (0:ℚ) ≤ 250)
      calc
        0 < (n:ℚ) := by positivity
        _ ≤ 250 * (4 * (m':ℚ) - n) := heq'l'
    have hnlt4m' : n < 4 * m' := by
      qify
      calc
        (n : ℚ) = 0 + n := by ring
        _ < 4 * (m':ℚ) - n + n := by rel [h4m'npos]
        _ = 4 * (m':ℚ) := by ring
    have h4m'npos' : 1 ≤ 4 * m' - n := by
      apply Nat.succ_le_of_lt
      apply Nat.lt_sub_of_add_lt
      simp [hnlt4m']
    -- we establish a lower bound of 125
    have hnlb1 : 125 < n := by
      apply Nat.lt_of_mul_lt_mul_left (a := 2)
      calc
        2 * 125 = 250 * 1 := by norm_num
        _ ≤ 250 * (4 * m' - n) := by rel [h4m'npos']
        _ < 2 * n := by
          qify; rw [Nat.cast_sub (le_of_lt hnlt4m')]; qify; exact heq'u'
    by_cases h127 : 127 ≤ n
    · exact h127
    -- and it remains to deal with the case that $n = 126$
    interval_cases n
    -- we consider the case where 4m' - n = 1
    -- but 4 is not a factor of 127
    by_cases h4m'n : 4 * m' - 126 ≤ 1
    · replace h4m'n := le_antisymm h4m'n h4m'npos'
      replace h4m'n := Nat.eq_add_of_sub_eq (le_of_lt hnlt4m') h4m'n
      have : 4 ∣ 127 := by
        rw [dvd_def]
        use m'
        rw [h4m'n]
      norm_num at this
    -- otherwise, 1 < 4m' - n
    push_neg at h4m'n
    replace h4m'n := Nat.succ_le_of_lt h4m'n
    qify [hnlt4m'] at h4m'n heq'u'
    have := calc
      (500:ℚ) = 250 * (1 + 1) := by ring
      _ ≤ 250 * (4 * (m':ℚ) - 126) := by rel [h4m'n]
      _ < 2 * 126 := heq'u'
    norm_num at this
