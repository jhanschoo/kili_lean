import Mathlib

open Real Set MeasureTheory

/- Let $S$ be the set of ordered pairs $(x, y)$ such that $0 < x \le 1, 0 < y ≤ 1,$ and $\left[\log_2{\left(\frac 1x\right)}\right]$ and $\left[\log_5{\left(\frac 1y\right)}\right]$ are both even. Given that the area of the graph of $S$ is $m/n,$ where $m$ and $n$ are relatively prime positive integers, find $m+n.$ The notation $[z]$ denotes the greatest integer that is less than or equal to $z.$ -/
theorem number_theory_98367
  {S : Set (ℝ × ℝ)}
  (hS : S = {(x, y) | 0 < x ∧ x ≤ 1 ∧ 0 < y ∧ y ≤ 1 ∧ Even ⌊logb 2 (1 / x)⌋ ∧ Even ⌊logb 5 (1 / y)⌋}) :
∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧ (volume S).toReal = m / n ∧ m + n = 14 := by
  -- observing that none of the conditions that define S simultaneously involve both components x and y of (x, y), we can consider S the product of its projections. Hence
  -- We first identify the projections of S in either coordinate.
  have {b x : ℝ} (hb : 1 < b) (hxl : 0 < x) (hxu : x ≤ 1) : Even ⌊logb b (1 / x)⌋ ↔ ∃ n, x ∈ Ioc (b ^ (2 * n + 1))⁻¹ (b ^ (2 * n))⁻¹ := by
    simp
    rw [even_iff_exists_two_nsmul]
    conv in (⌊-logb b x⌋ = 2 • _) =>
      rw [Int.floor_eq_iff, le_neg, neg_lt, lt_logb_iff_rpow_lt hb (by positivity), logb_le_iff_le_rpow hb (by positivity)]
      norm_cast
      simp [-neg_add_rev]
    constructor
    · intro ⟨c, hub, hlb⟩
      have hcnn := lt_of_lt_of_le hlb hxu
      rw [← zpow_neg, (by norm_num : 1 = b ^ (0:ℤ)),
        zpow_lt_zpow_iff_right₀ hb,
        neg_lt, neg_zero
      ] at hcnn
      replace hcnn := nonneg_of_mul_nonneg_right (Int.le_of_lt_add_one hcnn) (by norm_num)
      rw [← Int.toNat_of_nonneg hcnn] at hub hlb
      use c.toNat
      norm_cast at hub hlb ⊢
    · intro ⟨n, hlb, hub⟩
      use n
      norm_cast at hub hlb ⊢
  have {b x : ℝ} (hb : 1 < b) : 0 < x ∧ x ≤ 1 ∧ Even ⌊logb b (1 / x)⌋ ↔ ∃ n, x ∈ Ioc (b ^ (2 * n + 1))⁻¹ (b ^ (2 * n))⁻¹ := by
    constructor
    · intro ⟨hl, hu, h⟩
      exact (this hb hl hu).mp h
    · intro h
      have h' := h
      rcases h with ⟨n, hlb, hub⟩
      have hx : 0 < x ∧ x ≤ 1 := by
        have ppos : 0 < (b ^ (2 * n + 1))⁻¹ := (inv_pos_of_pos (pow_pos (by positivity) _))
        have pone : (b ^ (2 * n))⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (pow_pos (by positivity) _)]
          exact one_le_pow₀ (le_of_lt hb)
        exact ⟨lt_trans ppos hlb, le_trans hub pone⟩
      exact ⟨hx.1, hx.2, (this hb hx.1 hx.2).mpr h'⟩
  -- we now define the sets forming the projections
  set Sb := fun (b : ℝ) ↦ ⋃ (n : ℕ), Ioc (b ^ (2 * n + 1))⁻¹ (b ^ (2 * n))⁻¹ with hSb
  have hS' : S = Sb 2 ×ˢ Sb 5 := by
    rw [hS, hSb]
    ext x
    simp only [mem_setOf_eq, mem_prod, mem_iUnion]
    constructor
    · intro ⟨hxl, hxu, hyl, hyu, hx, hy⟩
      have hx' := (this (by norm_num)).mp ⟨hxl, hxu, hx⟩
      have hy' := (this (by norm_num)).mp ⟨hyl, hyu, hy⟩
      exact ⟨hx', hy'⟩
    · intro ⟨hx, hy⟩
      have hx' := (this (by norm_num)).mpr hx
      have hy' := (this (by norm_num)).mpr hy
      rcases hx' with ⟨hxl, hxu, hx''⟩
      rcases hy' with ⟨hyl, hyu, hy''⟩
      exact ⟨hxl, hxu, hyl, hyu, hx'', hy''⟩
  -- and note that the measure of these sets add up disjointly as a geometric series
  have hgs {b : ℝ} (hb : 1 < b) : (volume (Sb b)).toReal = (1 - b⁻¹) * (1 - b⁻¹ ^ 2)⁻¹ := by
    have hv (n : ℕ) : (b ^ (2 * n))⁻¹ - (b ^ (2 * n + 1))⁻¹ = (1 - b⁻¹) * (b⁻¹ ^ 2) ^ n :=
      calc
        (b ^ (2 * n))⁻¹ - (b ^ (2 * n + 1))⁻¹
          = (b ^ (2 * n + 1) - b ^ (2 * n)) / (b ^ (2 * n) * b ^ (2 * n + 1)) := by
            rw [inv_sub_inv (by positivity) (by positivity)]
        _ = ((b - 1) * b ^ (2 * n)) / (b ^ (2 * n) * b * b ^ (2 * n)) := by ring
        _ = (b - 1) / (b ^ (2 * n) * b) := by rw [mul_div_mul_right _ _ (by positivity)]
        _ = (b / b - b⁻¹) * (b⁻¹ ^ 2) ^ n := by ring
        _ = (1 - b⁻¹) * (b⁻¹ ^ 2) ^ n := by rw [div_self (by positivity)]
    calc
      (volume (Sb b)).toReal = (volume (⋃ n, Ioc (b ^ (2 * n + 1))⁻¹ (b ^ (2 * n))⁻¹)).toReal := by rw [hSb]
      _ = (∑' (n : ℕ), volume (Ioc (b ^ (2 * n + 1))⁻¹ (b ^ (2 * n))⁻¹)).toReal := by
        rw [measure_iUnion ?_ (by simp only [measurableSet_Ioc, implies_true])]
        rw [Symmetric.pairwise_on symmetric_disjoint]
        intro m n hmn
        replace hmn := Nat.succ_le_of_lt hmn
        replace hmn := (mul_le_mul_left (by norm_num : 0 < 2)).mpr hmn
        rw [Nat.mul_succ] at hmn
        simp only [Ioc_disjoint_Ioc, le_sup_iff, inf_le_iff]
        left; right
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        apply pow_le_pow_right₀ (le_of_lt hb) (le_trans (by linarith) hmn)
      _ = (∑' (n : ℕ), ENNReal.ofReal ((b ^ (2 * n))⁻¹ - (b ^ (2 * n + 1))⁻¹)).toReal := by
        simp only [volume_Ioc]
      _ = (∑' (n : ℕ), ENNReal.ofReal ((1 - b⁻¹) * (b⁻¹ ^ 2) ^ n)).toReal := by
        conv in (b ^ (2 * _))⁻¹ - (b ^ (2 * _ + 1))⁻¹ => rw [hv n]
      _ = (1 - b⁻¹) * (∑' (n : ℕ), ENNReal.ofReal ((b⁻¹ ^ 2)) ^ n).toReal := by
        conv in ENNReal.ofReal ((1 - b⁻¹) * (b⁻¹ ^ 2) ^ _) => rw [
          ENNReal.ofReal_mul (sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr (le_of_lt hb))), ENNReal.ofReal_pow (by positivity)]
        conv_lhs => rw [ENNReal.tsum_mul_left, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr (le_of_lt hb)))]
      _ = (1 - b⁻¹) * (1 - (b⁻¹ ^ 2))⁻¹ := by
        rw [ENNReal.tsum_geometric, ENNReal.toReal_inv,
          ENNReal.toReal_sub_of_le (by norm_num; rw [inv_le_one₀ (by positivity)]; exact one_le_pow₀ (le_of_lt hb)) (by norm_num),
          ENNReal.one_toReal, ENNReal.toReal_ofReal (by positivity)]
  -- Individually we obtain the following
  have hgs2 : (MeasureTheory.volume (Sb 2)).toReal = 2 / 3 := by
    rw [hgs (by norm_num : (1:ℝ) < 2)]
    norm_num
  have hgs5 : (MeasureTheory.volume (Sb 5)).toReal = 5 / 6 := by
    rw [hgs (by norm_num : (1:ℝ) < 5)]
    norm_num
  -- And obtain the main result, noting that 2 / 3 * 5 / 6 = 5 / 9
  have := calc
    (volume S).toReal = (volume ((Sb 2) ×ˢ (Sb 5))).toReal := by rw [hS']
    _ = (volume (Sb 2)).toReal * (volume (Sb 5)).toReal := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul]
    _ = 2 / 3 * (5 / 6) := by rw [hgs2, hgs5]
    _ = (5:ℕ) / (9:ℕ) := by norm_num
  exact ⟨5, 9, by norm_num, by norm_num, by norm_num, this, by norm_num⟩
