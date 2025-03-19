import Mathlib

open Real Set
open scoped BigOperators

/- For certain pairs $(m,n)$ of positive integers with $m\geq n$ there are exactly $50$ distinct positive integers $k$ such that $|\log m - \log k| < \log n$. Find the sum of all possible values of the product $mn$. -/
theorem number_theory_94240 :
  ∑' m : ℕ, ∑' n : ℕ,
    (if (m > 0 ∧ n > 0 ∧ m ≥ n ∧ {k : ℕ | 0 < k ∧ |log m - log k| < log n}.encard = 50) then
      m * n else 0) = 125 := by
  set P := fun (m n:ℕ) ↦ {k : ℕ | 0 < k ∧ |log m - log k| < log n}.encard = 50 with hP
  have hP' (m n:ℕ) : P m n = ({k : ℕ | 0 < k ∧ |log m - log ↑k| < log n}.encard = 50) := by rw [hP]
  conv_lhs =>
    arg 1
    ext m
    arg 1
    ext n
    arg 1
    arg 2
    arg 2
    arg 2
    rw [← hP']
  have hk {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) : |log m - log k| < log n ↔ (m:ℝ)/n < k ∧ (k:ℝ) < m * n := calc
    |log m - log k| < log n
      ↔ -log n < log m - log k ∧ log m - log k < log n := abs_lt
    _ ↔ log ((1:ℝ)/n) < log ((m:ℝ)/k) ∧ log ((m:ℝ)/k) < log n := by
      rw [← Real.log_inv, ← Real.log_div (by positivity) (by positivity)]
      field_simp
    _ ↔ (1:ℝ)/n < (m:ℝ)/k ∧ (m:ℝ)/k < n := by
      apply Iff.and <;> apply Real.log_lt_log_iff <;> positivity
    _ ↔ (k:ℝ) < m * n ∧ (m:ℝ)/n < k := by
      apply Iff.and
      · rw [div_lt_div_iff₀, one_mul] <;> positivity
      · apply div_lt_comm₀ <;> positivity
    _ ↔ (m:ℝ)/n < k ∧ (k:ℝ) < m * n := by rw [And.comm]
  have hcard (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≥ n) :
      P m n ↔ m * n - 51 = ⌊(m:ℝ)/n⌋₊ := by
    rw [hP']
    have hset : {k : ℕ | 0 < k ∧ |log m - log k| < log n} = Ioo ⌊(m:ℝ)/n⌋₊ (m * n) := by
      ext k; simp
      constructor
      · intro ⟨hpos, h⟩
        rw [hk hm hn hpos] at h
        norm_cast at h
        exact ⟨(Nat.floor_lt (by positivity)).mpr h.1, h.2⟩
      · intro ⟨hgt, h⟩
        have hpos : 0 < k := Nat.zero_lt_of_lt hgt
        specialize hk hm hn hpos
        exact ⟨hpos, hk.mpr ⟨(Nat.floor_lt (by positivity)).mp hgt, by norm_cast⟩⟩
    rw [hset, ← Finset.coe_Ioo, Set.encard_coe_eq_coe_finsetCard, Nat.card_Ioo]
    norm_cast
    have fl_pos : 0 < ⌊(m:ℝ)/n⌋₊ := by
      rw [Nat.floor_pos, one_le_div₀ (by positivity)]
      norm_cast
    omega
  have hn1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≥ n) (hP : P m n) : n ≠ 1 := by
    rw [hcard m n hm hn hmn] at hP
    intro contra
    subst contra
    simp at hP
    omega
  have hml (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≥ n) (hP : P m n) (hn' : 2 ≤ n) : (m:ℝ) ≤ 51 * n / (n * n - 1) ∧ (m:ℝ) > 50 * n / (n * n - 1) := by
    rw [hcard m n hm hn hmn] at hP
    have fl_pos : 0 < ⌊(m:ℝ)/n⌋₊ := by
      rw [Nat.floor_pos, one_le_div₀ (by positivity)]
      norm_cast
    have hprod : 51 ≤ m * n := by omega
    have hcond := hP.symm
    rw [Nat.floor_eq_iff (by positivity)] at hcond
    rify [hprod] at hcond
    constructor
    · have hcond := hcond.left
      rw [le_div_iff₀ (by positivity), sub_mul] at hcond
      rwa [le_div_iff₀ (by norm_num; rify at hn'; exact (lt_of_lt_of_le (by linarith : (1:ℝ) < 2 * 2)) (by rel [hn'])), mul_sub, ← mul_assoc, mul_one, sub_le_comm]
    · have hcond := hcond.right
      rw [div_lt_iff₀ (by positivity), add_mul, sub_mul, sub_add, ← sub_mul] at hcond
      norm_num at hcond
      rwa [gt_iff_lt, div_lt_iff₀ (by norm_num; rify at hn'; exact (lt_of_lt_of_le (by linarith : (1:ℝ) < 2 * 2)) (by rel [hn'])), mul_sub, ← mul_assoc, mul_one, lt_sub_comm]
  have hn2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≥ n) (neq : n = 2) : P m n ↔ m = 34 := by
    constructor
    · intro hP
      have hyp := hml m n hm hn hmn hP (by linarith)
      subst neq
      norm_num at hyp
      rcases lt_trichotomy m 34 with hm | hm | hm
      · have hm := Nat.le_pred_of_lt hm
        norm_num at hm
        rify at hm
        linarith
      · assumption
      · have hm := Nat.succ_le_of_lt hm
        norm_num at hm
        rify at hm
        linarith
    · intro hm
      rw [hcard m n (by omega) hn hmn]
      subst m n
      norm_num
  have hn3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≥ n) (neq : n = 3) : P m n ↔ m = 19 := by
    constructor
    · intro hP
      have hyp := hml m n hm hn hmn hP (by linarith)
      subst neq
      norm_num at hyp
      rcases lt_trichotomy m 19 with hm | hm | hm
      · have hm := Nat.le_pred_of_lt hm
        norm_num at hm
        rify at hm
        linarith
      · assumption
      · have hm := Nat.succ_le_of_lt hm
        norm_num at hm
        rify at hm
        linarith
    · intro hm
      rw [hcard m n (by omega) hn hmn]
      subst m n
      norm_num
      symm
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by linarith, by linarith⟩
  have hnle3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≥ n) (hP : P m n) (hn2 : 2 ≤ n) : n ≤ 3 := by
    have hyp := hml m n hm hn hmn hP hn2
    by_cases hn : n < 8
    · interval_cases n
        <;> [omega;omega;skip;skip;skip;skip]
        <;> norm_num at hyp
      -- n = 4
      · by_cases hm : m < 14
          <;> [have hm := Nat.le_pred_of_lt hm;skip]
          <;> norm_num at hm <;> rify at hm <;> linarith
      -- n = 5
      · by_cases hm : m < 11
          <;> [have hm := Nat.le_pred_of_lt hm;skip]
          <;> norm_num at hm <;> rify at hm <;> linarith
      -- n = 6
      · by_cases hm : m < 9
          <;> [have hm := Nat.le_pred_of_lt hm;skip]
          <;> norm_num at hm <;> rify at hm <;> linarith
      -- n = 7
      · by_cases hm : m < 8
          <;> [have hm := Nat.le_pred_of_lt hm;skip]
          <;> norm_num at hm <;> rify at hm <;> linarith
    · push_neg at hn
      rify at hn
      have :m < n := by
        rify
        calc
          (m:ℝ) ≤ 51 * ↑n / (↑n * ↑n - 1) := hyp.1
          _ < n := by
            rw [div_lt_iff₀, mul_comm, mul_lt_mul_left (by positivity)]
            calc
              51 < (8:ℝ) * 8 - 1 := by norm_num
              _ ≤ n * 8 - 1 := by rel [hn]
              _ ≤ n * n - 1 := by rel [hn]
            calc
              0 < (8:ℝ) * 8 - 1 := by norm_num
              _ ≤ n * 8 - 1 := by rel [hn]
              _ ≤ n * n - 1 := by rel [hn]
      omega
  conv_lhs =>
    arg 1
    ext m
    tactic =>
      rw [tsum_eq_sum (s:=({2, 3}:Finset ℕ))]
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at hn
      simp
      intro hm hn' hmn hcard'
      right
      specialize hn1 _ _ hm hn' hmn hcard'
      by_cases hn4 : 3 < n
      · specialize hnle3 _ _ hm hn' hmn hcard' (by omega)
        omega
      omega
  rw [tsum_eq_sum (s:=({19, 34}:Finset ℕ))]
  simp
  have h19_2 : ¬P 19 2 := by
    intro contra
    specialize hn2 19 2 (by positivity) (by positivity) (by norm_num) rfl
    tauto
  have h19_3 : P 19 3 := by
    specialize hn3 19 3 (by positivity) (by positivity) (by norm_num) rfl
    tauto
  have h34_2 : P 34 2 := by
    specialize hn2 34 2 (by positivity) (by positivity) (by norm_num) rfl
    tauto
  have h34_3 : ¬P 34 3 := by
    intro contra
    specialize hn3 34 3 (by positivity) (by positivity) (by norm_num) rfl
    tauto
  simp [h19_2, h19_3, h34_2, h34_3]
  simp
  intro m hm1 hm2
  constructor
  · intro hmpos hm2 hpm
    specialize hn2 m 2 hmpos (by positivity) hm2 rfl
    tauto
  · intro hmpos hm3 hpm
    specialize hn3 m 3 hmpos (by positivity) hm3 rfl
    tauto
