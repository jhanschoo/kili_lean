import Mathlib

set_option maxRecDepth 10000

theorem h (b i j : ℕ) : b ^ i * b ^ j = b ^ (i + j) := by exact Eq.symm (Nat.pow_add b i j)

/- How many positive integer multiples of $1001$ can be expressed in the form $10^{j} - 10^{i}$, where $i$ and $j$ are integers and $0\leq i < j \leq 99$? -/
theorem number_theory_97636 (P : ℕ → Prop) (hP : ∀ x, P x = ((∃ k > 0, x = 1001 * k) ∧ ∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ 99 ∧ x = 10 ^ j - 10 ^ i)) (S : Set ℕ) (hS : S = {x : ℕ | P x}) :
S.ncard = 784 := by
  have h10pos : 0 < 10 := by norm_num
  have h10 : 1 < 10 := by norm_num
  -- we show an identity quotienting $10^{6k+a}-1$ by $10^a$ for the next result
  have hfact (k a : ℕ) : 10 ^ (6 * k + a) - 1 = (10 ^ (6 * k) - 1) * 10 ^ a + (10 ^ a - 1) := calc
    10 ^ (6 * k + a) - 1 = 10 ^ (6 * k + a) - 10 ^ a + 10 ^ a - 1 := by
      rw [Nat.sub_add_cancel (by rw [pow_add]; exact Nat.le_mul_of_pos_left _ (by positivity))]
    _ = (10 ^ (6 * k) - 1) * 10 ^ a + (10 ^ a - 1) := by
      rw [pow_add, Nat.mul_sub_right_distrib, one_mul, Nat.add_sub_assoc (Nat.one_le_pow _ _ h10pos) _]
  have hdvd (t : ℕ) : 1001 ∣ 10 ^ t - 1 ↔ t % 6 = 0 := by
    rcases dvd_def.mp (nat_sub_dvd_pow_sub_pow (10 ^ 6) 1 (t / 6)) with ⟨k, hk⟩
    rw [one_pow] at hk
    calc
      1001 ∣ 10 ^ t - 1
        ↔ 1001 ∣ 10 ^ (6 * (t / 6) + t % 6) - 1 := by rw [mul_comm, (Nat.div_add_mod' t 6)]
      _ ↔ 1001 ∣ ((10 ^ 6) ^ (t / 6) - 1) * 10 ^ (t % 6) + (10 ^ (t % 6) - 1) := by rw [hfact, pow_mul]
      _ ↔ 1001 ∣ (10 ^ 6 - 1) * k * 10 ^ (t % 6) + (10 ^ (t % 6) - 1) := by rw [hk]
      _ ↔ 1001 ∣ 999 * k * 10 ^ (t % 6) * 1001 + (10 ^ (t % 6) - 1) := by nth_rw 1 [(by norm_num : 10 ^ 6 - 1 = 999 * 1001), mul_assoc 999, mul_comm 1001, ← mul_assoc 999, mul_assoc, mul_comm 1001, ← mul_assoc]
      _ ↔ 1001 ∣ 10 ^ (t % 6) - 1 := (Nat.dvd_add_iff_right (dvd_mul_left _ _)).symm
      _ ↔ 1 ≡ 10 ^ (t % 6) [MOD 1001] := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ h10pos)).symm
      _ ↔ t % 6 = 0 := by
        constructor <;> intro h
        · have : t % 6 < 6 := Nat.mod_lt _ (by positivity)
          interval_cases (t % 6)
          · rfl
          all_goals norm_cast at h
        · rw [h]
          rfl
  -- we now establish that we can count distinct (i, k) that satisfy conditions by drawing a bijection
  set f := fun (p : ℕ × ℕ) ↦ 10 ^ (p.1 + 6 * p.2) - 10 ^ p.1 with hf
  set S' := { p : ℕ × ℕ | 0 < p.2 ∧ p.1 + 6 * p.2 ≤ 99 } with hS'
  have heqv : Set.BijOn f S' S := by
    simp [hf, hS', hS, hP]
    refine ⟨?_, ?_, ?_⟩
    {
      simp [Set.MapsTo]
      intro i d hd hub
      · refine ⟨?_, i, i + 6 * d, (by linarith), hub, rfl⟩
        have hc := (hdvd (6 * d)).mpr (by norm_num)
        rcases hc with ⟨c, hc⟩
        have hpos : 0 < 1001 * c :=
          hc.symm ▸ Nat.zero_lt_sub_of_lt (Nat.one_lt_pow (mul_ne_zero (by norm_num) (ne_of_lt (Nat.zero_lt_sub_of_lt hd)).symm) h10)
        refine ⟨c * 10 ^ i, ?_, ?_⟩
        · refine (by norm_num : 0 = 0 / 1001) ▸ Nat.div_lt_of_lt_mul ?_
          calc
            0 < 1001 * c := hpos
            _ = 1001 * c * 1 := (mul_one _).symm
            _ ≤ 1001 * (c * 10 ^ i) := by rw [← mul_assoc]; exact Nat.mul_le_mul le_rfl (Nat.one_le_pow _ _ h10pos)
        · rw [← mul_assoc, ← hc, Nat.mul_sub_right_distrib, one_mul, ← pow_add, Nat.add_comm]
    }
    {
      have hjle (i j i' j' : ℕ) (hi'j' : i' < j') (hjj' : j < j') : 10 ^ j - 10 ^ i < 10 ^ j' - 10 ^ i' := calc
        10 ^ j - 10 ^ i < 10 ^ j := Nat.sub_lt (by positivity) (by positivity)
        _ ≤ 10 ^ (j' - 1) := pow_le_pow_right₀ h10pos (Nat.le_sub_one_of_lt hjj')
        _ = 10 ^ (j' - 1) * 1 := (mul_one _).symm
        _ ≤ 10 ^ (j' - 1) * (10 ^ 1 - 1) := by rel [(by norm_num : 1 ≤ 10 ^ 1 - 1)]
        _ = 10 ^ j' - 10 ^ (j' - 1) := by
          rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add, Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hi'j'))]
        _ ≤ 10 ^ j' - 10 ^ i' :=  Nat.sub_le_sub_left (Nat.pow_le_pow_right h10pos (Nat.le_sub_one_of_lt hi'j')) _
      have hile (i i' j : ℕ) (hij' : i < j) (hi'j' : i' < j) (hii' : i < i') : 10 ^ j - 10 ^ i' < 10 ^ j - 10 ^ i := Nat.sub_lt_sub_left (Nat.pow_lt_pow_right h10 hij') (Nat.pow_lt_pow_right h10 hii')
      simp [Set.InjOn]
      intro i d hij hub i' d' hi'j' hub' hinj
      rcases lt_trichotomy (i + 6 * d) (i' + 6 * d') with hjj' | hjj' | hjj'
      · specialize hjle i (i + 6 * d) i' (i' + 6 * d') (by linarith) hjj'; linarith
      · rw [hjj'] at hinj
        rcases lt_trichotomy i i' with hii' | rfl | hii'
        · specialize hile i i' (i' + 6 * d') (by linarith) (by linarith) hii'; linarith
        · exact ⟨rfl, Nat.mul_left_cancel (by positivity) (add_left_cancel hjj')⟩
        · specialize hile i' i (i' + 6 * d') (by linarith) (by linarith) hii'; linarith
      · specialize hjle i' (i' + 6 * d') i (i + 6 * d) (by linarith) hjj'; linarith
    }
    {
      simp [Set.SurjOn]
      rintro x ⟨⟨k, kpos, hxk⟩, ⟨i, j, hij, hub, hxij⟩⟩
      simp
      have h6 : 6 ∣ j - i := by
        refine (Nat.dvd_of_mod_eq_zero ((hdvd _).mp ?_))
        -- First, $1001k = 10^i(10^{j - i} - 1)$.
        have this : 1001 * k = 10 ^ i * (10 ^ (j - i) - 1) := by
          rw [← hxk, hxij, Nat.mul_sub, ← Nat.pow_add, Nat.add_sub_of_le (le_of_lt hij), mul_one]
        -- On the other hand, 1001 and 10^i are coprime,
        have hcop10 (i : ℕ) : (1001).Coprime (10 ^ i) := by
          apply Nat.Coprime.pow_right i
          -- it suffices to show that (7 * 11 * 13) and (2 * 5) are coprime,
          -- being the respective prime factorizations of 1001 and 10
          suffices ((7 * 11 * 13).Coprime (2 * 5)) by refine this
          refine Nat.Coprime.mul_right ?_ ?_ <;>
          refine Nat.Coprime.mul (Nat.Coprime.mul ?_ ?_) ?_ <;>
          exact Nat.coprime_of_lt_prime (by positivity) (by norm_num) (by norm_num)
        -- Together we obtain the result $1001 | 10^{j-i} - 1$.
        exact Nat.Coprime.dvd_of_dvd_mul_left (hcop10 i) (Dvd.intro k this)
      have hj : i + 6 * ((j - i) / 6) = j := by
        rw [Nat.mul_div_eq_iff_dvd.mpr h6, add_comm, Nat.sub_add_cancel (le_of_lt hij)]
      refine ⟨i, (j - i) / 6, ⟨?_, ?_⟩, ?_⟩
      · refine Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_sub_of_lt hij) h6) (by norm_num)
        -- refine ⟨i, (j - i) / 6, ⟨⟨Nat.zero_lt_sub_of_lt hij, (Nat.add_sub_of_le (Nat.le_of_lt hij)).symm ▸ hub, (hdvd (j - i)).mp ?_⟩, (Nat.add_sub_of_le (Nat.le_of_lt hij)).symm ▸ hxij.symm⟩⟩
      · rwa [hj]
      · rw [hj, hxij]
    }
  calc
    -- Finally, we perform some algebraic manipulation to obtain the answer,
    --   observing that 1 ≤ k ≤ 16, and to each distinct k, the pairs are distinct
    --   and we can treat it as a disjoint union (with k ranging) of sets of pairs
    --   (i, k) in which the i range.
    S.ncard = S'.ncard := by
      rw [← Set.BijOn.image_eq heqv, Set.ncard_image_of_injOn heqv.injOn]
    _ = { p ∈ Finset.Icc 0 99 ×ˢ Finset.Icc 1 16 | 0 < p.2 ∧ p.1 + 6 * p.2 ≤ 99 }.card := by
      rw [← Set.ncard_coe_Finset]
      congr
      ext ⟨i, d⟩
      simp only [hS', Set.mem_setOf_eq, Finset.coe_filter, iff_and_self, and_imp]
      intro hdpos hub
      simp only [Finset.mem_product, Finset.mem_Icc, zero_le, true_and]
      refine ⟨Nat.le_of_add_right_le hub, Nat.succ_le_of_lt hdpos, ?_⟩
      apply Nat.le_of_lt_succ
      refine Nat.lt_of_mul_lt_mul_left (?_ : 6 * d < 6 * 17)
      refine Nat.lt_of_le_of_lt (Nat.le_of_add_right_le (add_comm i _ ▸ hub) : 6 * d ≤ 99) (by norm_num)
    _ = ∑ u ∈ Finset.Icc 1 16, { a ∈ Finset.Icc 0 99 | 0 < u ∧ a + 6 * u ≤ 99 }.card := by
      nth_rw 1 [Finset.product_eq_biUnion_right, Finset.filter_biUnion, Finset.card_biUnion]
      conv_lhs =>
        arg 2
        ext u
        arg 1
        rw [Finset.filter_image]
        simp
      have (u : ℕ) : (fun (a : ℕ) ↦ (a, u)).Injective := by
        intro a a' hinj
        simp at hinj
        exact hinj
      conv_lhs =>
        arg 2
        ext u
        rw [Finset.card_image_of_injective _ (this u)]
      intro x _ y _ hxy
      apply Finset.disjoint_filter_filter
      contrapose hxy
      simp only [ne_eq, Decidable.not_not]
      rw [Finset.not_disjoint_iff] at hxy
      rcases hxy with ⟨p, hpl, hpr⟩
      rw [Finset.mem_image] at hpl hpr
      rcases hpl with ⟨a, _, hpl⟩
      rcases hpr with ⟨b, _, hpr⟩
      simp [← hpr, Prod.eq_iff_fst_eq_snd_eq] at hpl
      exact hpl.2
    _ = ∑ u ∈ Finset.Icc 1 16, (Finset.Icc 0 (99 - 6 * u)).card := by
      apply Finset.sum_congr rfl
      intro k hk
      congr
      ext i
      simp at hk ⊢
      constructor
      · intro ⟨hub, hpos, heq⟩
        exact Nat.le_sub_of_add_le heq
      · intro heq
        refine ⟨le_trans heq (by norm_num), Nat.lt_of_succ_le hk.1, Nat.add_le_of_le_sub ?_ heq⟩
        calc
          6 * k ≤ 6 * 16 := by rel [hk.2]
          _ ≤ 99 := by norm_num
    _ = 784 := by
      simp
      iterate 16 rw [Finset.sum_Icc_succ_top (by norm_num)]
      simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, zero_add, mul_one,
        Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul]
