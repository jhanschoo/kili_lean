import Mathlib

open Real Set
open scoped BigOperators

/- Find the number of pairs $(m,n)$ of positive integers with $1\le m < n\le 30$ such that there exists a real number $x$ satisfying
$$
\sin(mx)+\sin(nx)=2.
$$
 -/
theorem number_theory_98501 :
    {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m < n ∧ n ≤ 30 ∧ ∃ x : ℝ, sin (m * x) + sin (n * x) = 2}.encard = 63 := by
  have (m n : ℕ) : (1 ≤ m ∧ m < n ∧ n ≤ 30 ∧ ∃ x : ℝ, sin (m * x) + sin (n * x) = 2) ↔ (m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ m < n ∧ ∃ a b : ℤ, (1 + 4 * b) * m = (1 + 4 * a) * n) := by
    constructor
    · rintro ⟨mpos, hmn, n30, x, hx⟩
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hmn, ?_⟩
      have hsinm : sin (m * x) = 1 := by
        refine le_antisymm (Real.sin_le_one _) (le_of_add_le_add_right (a := sin (n * x)) ?_)
        rw [hx, (by norm_num : (2:ℝ)=1+1)]
        rel [Real.sin_le_one _]
      have hsinn : sin (n * x) = 1 := by linarith
      obtain ⟨a, ha⟩ := Real.sin_eq_one_iff.mp hsinm
      obtain ⟨b, hb⟩ := Real.sin_eq_one_iff.mp hsinn
      have hxn0 : x ≠ 0 := by intro contra; simp [contra] at hsinm
      have : (1 + 4 * b) * (m * x) = (1 + 4 * a) * (n * x) := by rw [← ha, ← hb]; ring
      rw [← mul_assoc, ← mul_assoc] at this
      apply mul_right_cancel₀ hxn0 at this
      use a, b
      norm_cast at this
    · rintro ⟨hm, hn, hmn, a, b, h⟩
      have hm1 := (Finset.mem_Icc.mp hm).1
      have hn1 := (Finset.mem_Icc.mp hn).1
      refine ⟨hm1, hmn, (Finset.mem_Icc.mp hn).2, ?_⟩
      set x := (1 + 4 * b) / n * (π / 2) with hx
      have hx' : x = (1 + 4 * a) / m * (π / 2) := by
        rw [hx]
        congr 1
        field_simp
        norm_cast
      use x
      have : sin (m * x) = 1 := by
        rw [Real.sin_eq_one_iff]
        use a
        rw [hx']
        field_simp
        ring
      have : sin (n * x) = 1 := by
        rw [Real.sin_eq_one_iff]
        use b
        rw [hx]
        field_simp
        ring
      linarith
  -- set S := { p ∈ Finset.Icc (1:ℕ) 30 ×ˢ Finset.Icc (1:ℕ) 30 | p.1 < p.2 ∧ ∃ a b : ℤ, (1 + 4 * b) * p.1 = (1 + 4 * a) * p.2 } with hS
  -- have : {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m < n ∧ n ≤ 30 ∧ ∃ x : ℝ, sin (m * x) + sin (n * x) = 2} = S := by
  have hmod (m n : ℕ) (hmp : 0 < m) (hnp : 0 < n) : ((m < n) ∧ ∃ (a b : ℤ), (1 + 4 * b) * m = (1 + 4 * a) * n) ↔ (∃ m' n' p, m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ ((m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4]) ∨ (m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4]))) := by
    constructor
    · intro ⟨hmn, a, b, h⟩
      set p := m.factorization 2 with hp
      set m' := m / 2 ^ p with hm'
      set n' := n / 2 ^ p with hn'
      use m', n', p
      have m'_valid : 2 ^ p * m' = m := by
        rw [hm', hp, Nat.mul_div_eq_iff_dvd]
        exact (Nat.ordProj_dvd _ _)
      have n'_valid : 2 ^ p * n' = n := by
        rw [hn', hp, Nat.mul_div_eq_iff_dvd]
        zify
        -- dvd gcd mul
        have : Int.gcd (2 ^ p) (1 + 4 * a)  = 1 := by
          rw [← Int.isCoprime_iff_gcd_eq_one]
          apply IsCoprime.pow_left
          apply IsRelPrime.isCoprime
          rw [(by ring : 4 * a = 2 * (2 * a)), IsRelPrime.add_mul_left_right_iff]
          exact isRelPrime_one_right
        have hdvd : 2 ^ p ∣ (1 + 4 * a) * n := by
          rw [← h]
          apply dvd_mul_of_dvd_right
          rw [dvd_def]
          use m'
          symm
          norm_cast
        exact Int.dvd_of_dvd_mul_right_of_gcd_one hdvd this
      have two_ndvd_m' : ¬2 ∣ m' := by
        intro this
        rw [← pow_one 2] at this
        have := mul_dvd_mul_left (2 ^ p) this
        rw [m'_valid, ← pow_add, hp] at this
        exact Nat.pow_succ_factorization_not_dvd (by positivity) (by norm_num) this
      have m'_lt_n' : m' < n' := by
        rwa [← m'_valid, ← n'_valid, mul_lt_mul_iff_of_pos_left (by positivity)] at hmn
      have hmnmod : m' ≡ n' [MOD 4] := by
        rw [← m'_valid, ← n'_valid, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, mul_comm _ (m':ℤ), mul_comm _ (n':ℤ), ← mul_assoc, ← mul_assoc, Int.mul_eq_mul_right_iff (by positivity)] at h
        rw [← Int.natCast_modEq_iff]
        calc
          (m':ℤ) ≡ m' + 4 * (b * m') [ZMOD 4] := Int.modEq_add_fac_self.symm
          _ = (1 + 4 * b) * m' := by ring
          _ = (1 + 4 * a) * n' := h
          _ = n' + 4 * (a * n') := by ring
          _ ≡ n' [ZMOD 4] := Int.modEq_add_fac_self
      have two_ndvd_n' : ¬2 ∣ n' := by
        zify at two_ndvd_m'
        rw [(by norm_num : 4 = 2 * 2)] at hmnmod
        apply Nat.ModEq.of_mul_left at hmnmod
        intro this
        rw [(by norm_num : n' = n' - 0)] at this
        rw [← Nat.modEq_iff_dvd' (by positivity)] at this
        have := this.trans hmnmod.symm
        rw [Nat.modEq_iff_dvd] at this
        norm_num at this
        tauto
        -- TODO
      refine ⟨m'_valid.symm, n'_valid.symm, two_ndvd_m', two_ndvd_n', m'_lt_n', ?_⟩
      zify at two_ndvd_m'
      mod_cases hm'mod : m' % 4
      · rw [Nat.modEq_iff_dvd] at hm'mod
        norm_num at hm'mod
        rw [(by norm_num : (4:ℤ) = 2 * 2)] at hm'mod
        apply dvd_of_mul_right_dvd at hm'mod
        tauto
      · left
        exact ⟨hm'mod, hmnmod.symm.trans hm'mod⟩
      · rw [Nat.modEq_iff_dvd] at hm'mod
        norm_num at hm'mod
        rw [(by norm_num : (4:ℤ) = 2 * 2)] at hm'mod
        apply dvd_of_mul_right_dvd at hm'mod
        apply Int.dvd_iff_dvd_of_dvd_sub at hm'mod
        tauto
      · right
        exact ⟨hm'mod, hmnmod.symm.trans hm'mod⟩
    · rintro ⟨m', n', p, m'valid, n'valid, odd_m', odd_n', m'_lt_n', hmod⟩
      have m_lt_n : m < n := by
        rwa [m'valid, n'valid, mul_lt_mul_iff_of_pos_left (by positivity)]
      refine ⟨m_lt_n, ?_⟩
      conv =>
        arg 1
        ext a
        arg 1
        ext b
        rw [m'valid, n'valid,
          Nat.cast_mul,
          Nat.cast_mul,
          mul_comm _ (m':ℤ),
          mul_comm _ (n':ℤ),
          ← mul_assoc,
          ← mul_assoc,
          Int.mul_eq_mul_right_iff (by positivity)
        ]
      rw [
        @Nat.ModEq.comm _ m' 1,
        @Nat.ModEq.comm _ n' 1,
        @Nat.ModEq.comm _ m' 3,
        @Nat.ModEq.comm _ n' 3,
      ] at hmod
      simp_rw [Nat.modEq_iff_dvd, dvd_def] at hmod
      norm_num at hmod
      rcases hmod with ⟨⟨a', hmodm'⟩, ⟨b', hmodn'⟩⟩ | ⟨⟨a', hmodm'⟩, ⟨b', hmodn'⟩⟩
      · use a', b'
        rw [sub_eq_iff_eq_add'] at hmodm' hmodn'
        rw [hmodm', hmodn']
        ring
      · rw [sub_eq_iff_eq_add'] at hmodm' hmodn'
        rw [hmodm', hmodn']
        use (-(1+a')), (-(1+b'))
        ring
  convert_to { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ (m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] ∨ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4]) }.encard = 63
  · congr
    ext ⟨m, n⟩
    simp only [mem_setOf_eq]
    constructor
    · rintro h
      have := (this m n).mp h
      refine ⟨this.1, this.2.1, ?_⟩
      exact (hmod m n (Nat.lt_of_succ_le h.1) (lt_trans (Nat.lt_of_succ_le h.1) h.2.1)).mp ⟨h.2.1, this.2.2.2⟩
    · rintro ⟨hm, hn, h⟩
      have ⟨m', n', p, hm', hn', m'_odd, n'_odd, hm'n', hmod'⟩ := h
      have hmb := Finset.mem_Icc.mp hm
      have hnb := Finset.mem_Icc.mp hn
      have hmn : m < n := by rwa [hm', hn', mul_lt_mul_iff_of_pos_left (by positivity)]
      refine ⟨hmb.1, hmn, hnb.2, ?_⟩
      have h' := (hmod _ _ (Nat.lt_of_succ_le hmb.1) (Nat.lt_of_succ_le hnb.1)).mpr h
      have h' := (this m n).mpr ⟨hm, hn, hmn, h'.2⟩
      exact h'.2.2.2
  convert_to
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard
      +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard
      = 63
  · rw [← encard_union_eq]
    · congr
      ext ⟨m, n⟩
      simp only [mem_setOf_eq, mem_union]
      constructor
      · rintro ⟨hm, hn, m', n', p, hm', hn', hm'odd, hn'odd, hm'n', hmod | hmod⟩
        · exact Or.inl ⟨hm, hn, m', n', p, hm', hn', hm'odd, hn'odd, hm'n', hmod⟩
        · exact Or.inr ⟨hm, hn, m', n', p, hm', hn', hm'odd, hn'odd, hm'n', hmod⟩
      · intro h
        rcases h with ⟨hm, hn, m', n', p, hm', hn', hm'odd, hn'odd, hm'n', hmod⟩ | ⟨hm, hn, m', n', p, hm', hn', hm'odd, hn'odd, hm'n', hmod⟩
        · exact ⟨hm, hn, m', n', p, hm', hn', hm'odd, hn'odd, hm'n', Or.inl hmod⟩
        · exact ⟨hm, hn, m', n', p, hm', hn', hm'odd, hn'odd, hm'n', Or.inr hmod⟩
    · intro nset il ir
      simp only [le_eq_subset, bot_eq_empty, subset_empty_iff] at il ir ⊢
      rw [Set.eq_empty_iff_forall_not_mem]
      intro ⟨m, n⟩ hp
      specialize il hp
      specialize ir hp
      simp only [mem_setOf_eq] at il ir
      rcases il with ⟨_, _, m', _, p', hm', _, hm'odd, _, _, hmod', _⟩
      rcases ir with ⟨_, _, m'', _, p'', hm'', _, hm''odd, _, _, hmod'', _⟩
      rw [hm''] at hm'
      have : m'' = m' := by
        apply dvd_antisymm
        · have : m'' ∣ 2 ^ p' * m' := Dvd.intro_left _ hm'
          refine Nat.Coprime.dvd_of_dvd_mul_left ?_ this
          exact Nat.Prime.coprime_pow_of_not_dvd (by norm_num) hm''odd
        · have : m' ∣ 2 ^ p'' * m'' := Dvd.intro_left _ hm'.symm
          refine Nat.Coprime.dvd_of_dvd_mul_left ?_ this
          exact Nat.Prime.coprime_pow_of_not_dvd (by norm_num) hm'odd
      rw [this] at hmod''
      have := hmod''.symm.trans hmod'
      norm_cast at this
  -- we perform case and bounds analysis on p=0, 1, 2, >2. The on the LHS of these equations are disjoint, because m is divided by different greatest powers of 2 across these sets. Then their cardinality is equal to the RHS because with (m, n) and p determined in each case, m' and n' are determined as well, and must satisfy the tighter bounds.
  have set1_p0 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^0 * m' ∧ n = 2^0 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 30 ∧ n ∈ Finset.Ioc 0 30 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard := by sorry
  have set1_p0' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 30 ∧ n ∈ Finset.Ioc 0 30 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 30 | m ≡ 1 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set1_p1 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^1 * m' ∧ n = 2^1 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 15 ∧ n ∈ Finset.Ioc 0 15 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard := by sorry
  have set1_p1' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 15 ∧ n ∈ Finset.Ioc 0 15 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 15 | m ≡ 1 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set1_p2 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^2 * m' ∧ n = 2^2 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 7 ∧ n ∈ Finset.Ioc 0 7 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard := by sorry
  have set1_p2' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 7 ∧ n ∈ Finset.Ioc 0 7 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 7 | m ≡ 1 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set1_p3 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^3 * m' ∧ n = 2^3 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 3 ∧ n ∈ Finset.Ioc 0 3 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard := by sorry
  have set1_p3' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 3 ∧ n ∈ Finset.Ioc 0 3 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 3 | m ≡ 1 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set1_p4 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^4 * m' ∧ n = 2^4 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 1 ∧ n ∈ Finset.Ioc 0 1 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard := by sorry
  have set1_p4' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 1 ∧ n ∈ Finset.Ioc 0 1 ∧ m < n ∧ m ≡ 1 [MOD 4] ∧ n ≡ 1 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 1 | m ≡ 1 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set1_pgt4 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, 4 < p ∧ m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard = 0 := by sorry
  have set1_eq :
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard =
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^0 * m' ∧ n = 2^0 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^1 * m' ∧ n = 2^1 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^2 * m' ∧ n = 2^2 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^3 * m' ∧ n = 2^3 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^4 * m' ∧ n = 2^4 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, 4 < p ∧ m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 1 [MOD 4] ∧ n' ≡ 1 [MOD 4] }.encard := by sorry
  rw [set1_eq, set1_pgt4, set1_p4, set1_p4', set1_p3, set1_p3', set1_p2, set1_p2', set1_p1, set1_p1', set1_p0, set1_p0']
  rw [Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _]
  have set3_p0 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^0 * m' ∧ n = 2^0 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 30 ∧ n ∈ Finset.Ioc 0 30 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard := by sorry
  have set3_p0' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 30 ∧ n ∈ Finset.Ioc 0 30 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 30 | m ≡ 3 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set3_p1 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^1 * m' ∧ n = 2^1 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 15 ∧ n ∈ Finset.Ioc 0 15 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard := by sorry
  have set3_p1' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 15 ∧ n ∈ Finset.Ioc 0 15 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 15 | m ≡ 3 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set3_p2 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^2 * m' ∧ n = 2^2 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 7 ∧ n ∈ Finset.Ioc 0 7 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard := by sorry
  have set3_p2' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 7 ∧ n ∈ Finset.Ioc 0 7 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 7 | m ≡ 3 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set3_p3 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^3 * m' ∧ n = 2^3 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 3 ∧ n ∈ Finset.Ioc 0 3 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard := by sorry
  have set3_p3' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 3 ∧ n ∈ Finset.Ioc 0 3 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 3 | m ≡ 3 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set3_p4 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^4 * m' ∧ n = 2^4 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard =
    { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 1 ∧ n ∈ Finset.Ioc 0 1 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard := by sorry
  have set3_p4' : { (m, n) : ℕ × ℕ | m ∈ Finset.Ioc 0 1 ∧ n ∈ Finset.Ioc 0 1 ∧ m < n ∧ m ≡ 3 [MOD 4] ∧ n ≡ 3 [MOD 4] }.encard =
    ({ m ∈ Finset.Ioc 0 1 | m ≡ 3 [MOD 4] }.card:ℤ).natAbs.choose 2 := by sorry
  have set3_pgt4 :
    { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, 4 < p ∧ m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard = 0 := by sorry
  have set3_eq :
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard =
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^0 * m' ∧ n = 2^0 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^1 * m' ∧ n = 2^1 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^2 * m' ∧ n = 2^2 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^3 * m' ∧ n = 2^3 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n', m = 2^4 * m' ∧ n = 2^4 * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard +
      { (m, n) : ℕ × ℕ | m ∈ Finset.Icc 1 30 ∧ n ∈ Finset.Icc 1 30 ∧ ∃ m' n' p, 4 < p ∧ m = 2^p * m' ∧ n = 2^p * n' ∧ ¬2 ∣ m' ∧ ¬2 ∣ n' ∧ m' < n' ∧ m' ≡ 3 [MOD 4] ∧ n' ≡ 3 [MOD 4] }.encard := by sorry
  rw [set3_eq, set3_pgt4, set3_p4, set3_p4', set3_p3, set3_p3', set3_p2, set3_p2', set3_p1, set3_p1', set3_p0, set3_p0']
  rw [Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _, Nat.Ioc_filter_modEq_card _ _ (by norm_num : 0 < 4) _]
  norm_num
  norm_cast
