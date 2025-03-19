import Mathlib

/- Let $\mathcal{S}$ be the set of real numbers that can be represented as repeating decimals of the form $0.\overline{abc}$ where $a, b, c$ are distinct digits. Find the sum of the elements of $\mathcal{S}.$ -/
theorem number_theory_93120 (S : Set ℝ) (hS : S = { x ∈ Set.Icc (0 : ℝ) 1 | ∃ a ∈ Finset.range 10, ∃ b ∈ Finset.range 10, ∃ c ∈ Finset.range 10, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x = (a * 100 + b * 10 + c) / 999 }) :
    ∑ᶠ x ∈ S, x = 360 := by
  have nesymm {a b : ℕ} (h : ¬ a = b) : ¬ b = a := fun a ↦ h a.symm
  -- Consider the set of triples of distinct digits (a, b, c)
  set T := (Finset.range 10).biUnion (fun a ↦ {a} ×ˢ (Finset.range 10 \ {a}).biUnion (fun b ↦ {b} ×ˢ ((Finset.range 10 \ {a}) \ {b}).biUnion (fun c ↦ {c}))) with hT
  -- Observe that these triples of distinct digits are in bijection with the target set with each triple $(a,b,c)$ mapped to $0.\overline{abc}$.
  set f := fun ((a, b, c) : ℕ × ℕ × ℕ) ↦ ((a:ℝ) * 100 + b * 10 + c) / 999 with hf
  have hfT : Set.BijOn f T S := by
    simp only [Set.BijOn, Set.MapsTo, hT, Finset.biUnion_singleton_eq_self,
      Finset.singleton_product, Finset.coe_biUnion, Finset.coe_range, Set.mem_Iio, Finset.coe_map,
      Function.Embedding.coeFn_mk, Finset.coe_sdiff, Finset.coe_singleton, Set.mem_diff,
      Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image, exists_prop, Prod.exists, Prod.mk.injEq,
      exists_eq_right_right, hS, Set.mem_Icc, Finset.mem_range, ne_eq, hf, Set.mem_setOf_eq,
      forall_exists_index, and_imp, Prod.forall, Set.InjOn, Set.SurjOn]
    refine ⟨?_, ?_, ?_⟩
    {
      intro a' b' c' a ha b c hb hab hc hac hbc haa' hbb' hcc'
      subst a' b' c'
      refine ⟨⟨?_, ?_⟩, a, ha, b, hb, c, hc,
        nesymm hab, nesymm hac, nesymm hbc, rfl⟩
      · exact div_nonneg (by positivity) (by norm_num)
      · rw [div_le_iff₀ (by positivity), one_mul]
        norm_cast
        omega
    }
    {
      intro a' b' c' a ha b c hb hab hc hac hbc haa' hbb' hcc'
      subst a' b' c'
      intro a'' b'' c'' a' ha' b' c' hb' ha'b' hc' ha'c' hb'c' ha'a'' hb'b'' hc'c''
      subst a'' b'' c''
      intro heq
      rw [div_eq_div_iff (by positivity) (by positivity), mul_eq_mul_right_iff] at heq
      rcases heq with heq | habsurd <;> [skip; norm_num at habsurd]
      norm_cast at heq
      omega
    }
    {
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_iUnion, Set.mem_diff, Set.mem_Iio,
        Set.mem_singleton_iff, exists_prop, Prod.exists, Prod.mk.injEq,
        exists_eq_right_right] at hx ⊢
      rcases hx with ⟨⟨hxl, hxu⟩, a, ha, b, hb, c, hc, hab, hac, hbc, heq⟩
      exact ⟨a, b, c, ⟨a, ha, b, c, ⟨⟨hb, nesymm hab⟩, ⟨hc, nesymm hac⟩, nesymm hbc⟩, rfl, rfl, rfl⟩, heq.symm⟩
    }
  -- But we obtain another bijection mapping each $(a,b,c)$ to $0.\overline{(9-a)(9-b)(9-c)}$.
  set g := fun ((a, b, c) : ℕ × ℕ × ℕ) ↦ ((9-(a:ℝ)) * 100 + (9-b) * 10 + (9-c)) / 999 with hg
  have hgT : Set.BijOn g T S := by
    simp only [Set.BijOn, Set.MapsTo, hT, Finset.biUnion_singleton_eq_self,
      Finset.singleton_product, Finset.coe_biUnion, Finset.coe_range, Set.mem_Iio, Finset.coe_map,
      Function.Embedding.coeFn_mk, Finset.coe_sdiff, Finset.coe_singleton, Set.mem_diff,
      Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image, exists_prop, Prod.exists, Prod.mk.injEq,
      exists_eq_right_right, hS, Set.mem_Icc, Finset.mem_range, ne_eq, hg, Set.mem_setOf_eq,
      forall_exists_index, and_imp, Prod.forall, Set.InjOn, Set.SurjOn]
    refine ⟨?_, ?_, ?_⟩
    {
      intro a' b' c' a ha b c hb hab hc hac hbc haa' hbb' hcc'
      subst a' b' c'
      replace ha := Nat.le_of_lt_succ ha
      replace hb := Nat.le_of_lt_succ hb
      replace hc := Nat.le_of_lt_succ hc
      refine ⟨⟨?_, ?_⟩,
        9 - a, Nat.sub_lt_succ _ _,
        9 - b, Nat.sub_lt_succ _ _,
        9 - c, Nat.sub_lt_succ _ _,
        by omega, by omega, by omega, ?_⟩
      · rify at ha hb hc
        linarith
      · rw [div_le_iff₀ (by positivity), one_mul]
        linarith
      · rw [Nat.cast_sub ha, Nat.cast_sub hb, Nat.cast_sub hc]
        norm_cast
    }
    {
      intro a' b' c' a ha b c hb hab hc hac hbc haa' hbb' hcc'
      subst a' b' c'
      intro a'' b'' c'' a' ha' b' c' hb' ha'b' hc' ha'c' hb'c' ha'a'' hb'b'' hc'c''
      subst a'' b'' c''
      replace ha := Nat.le_of_lt_succ ha
      replace hb := Nat.le_of_lt_succ hb
      replace hc := Nat.le_of_lt_succ hc
      replace ha' := Nat.le_of_lt_succ ha'
      replace hb' := Nat.le_of_lt_succ hb'
      replace hc' := Nat.le_of_lt_succ hc'
      intro heq
      rw [div_eq_div_iff (by positivity) (by positivity), mul_eq_mul_right_iff] at heq
      rcases heq with heq | habsurd <;> [skip; norm_num at habsurd]
      norm_cast at heq
      omega
    }
    {
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_iUnion, Set.mem_diff, Set.mem_Iio,
        Set.mem_singleton_iff, exists_prop, Prod.exists, Prod.mk.injEq,
        exists_eq_right_right] at hx ⊢
      rcases hx with ⟨⟨hxl, hxu⟩, a, ha, b, hb, c, hc, hab, hac, hbc, heq⟩
      replace ha := Nat.le_of_lt_succ ha
      replace hb := Nat.le_of_lt_succ hb
      replace hc := Nat.le_of_lt_succ hc
      refine ⟨9 - a, 9 - b, 9 - c,
        ⟨9 - a, Nat.sub_lt_succ _ _, 9 - b, 9 - c, ⟨
          ⟨Nat.sub_lt_succ _ _, by omega⟩, ⟨Nat.sub_lt_succ _ _, by omega⟩, by omega⟩, rfl, rfl, rfl⟩,
      ?_⟩
      rw [
        (by rw [Nat.cast_sub ha]; norm_num : (9 - (9 - a : ℕ) : ℝ) = a),
        (by rw [Nat.cast_sub hb]; norm_num : (9 - (9 - b : ℕ) : ℝ) = b),
        (by rw [Nat.cast_sub hc]; norm_num : (9 - (9 - c : ℕ) : ℝ) = c),
        heq
      ]
    }
  -- so for the same triple (a,b,c), if we should sum up the two real numbers that it
  -- gets mapped to under the two different bijections, we get $0.\overline{abc}+0.\overline{(9-a)(9-b)(9-c)}=0.\overline{999}=1$
  have hfg : ∀ t ∈ T, f t + g t = 1 := by
    intro t ht
    simp only [hT, Finset.biUnion_singleton_eq_self, Finset.singleton_product, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_map, Finset.mem_sdiff, Finset.mem_singleton,
      Function.Embedding.coeFn_mk, Prod.exists, Prod.mk.injEq, exists_eq_right_right, hf,
      hg] at ht ⊢
    rcases ht with ⟨a, ha, b, c, ⟨⟨hb, hab⟩, ⟨hc, hac⟩, hbc⟩, ht⟩
    linarith
  have hSFinite : S.Finite :=
    Set.Finite.of_surjOn _ hfT.2.2 (Finset.finite_toSet _)
  -- Moreover, our set of triples has cardinaility 10 * 9 * 8 = 720, which is the
  -- number of ways to choose the first digit, then a distinct second digit, then
  -- a distinct third digit.
  have hTcard : T.card = 720 := by
    conv_lhs =>
      rw [hT, Finset.card_biUnion (by
        intro x hx y hy hxy
        rw [Finset.disjoint_product]
        left
        rwa [Finset.disjoint_singleton]
      )]
      arg 2
      ext a
      rw [Finset.card_product, Finset.card_singleton, one_mul, Finset.card_biUnion (by
        intro x hx y hy hxy
        rw [Finset.disjoint_product]
        left
        rwa [Finset.disjoint_singleton]
      )]
      arg 2
      ext b
      rw [Finset.card_product, Finset.card_singleton, one_mul, Finset.card_biUnion (by
        intro x hx y hy hxy
        rwa [Finset.disjoint_singleton]
      )]
      arg 2
      ext c
      rw [Finset.card_singleton]
    rw [Finset.sum_eq_card_nsmul (b := 72)]
    · norm_num
    intro a ha
    rw [Finset.sum_eq_card_nsmul (b := 8)]
    · rw [Finset.card_sdiff, Finset.card_range, Finset.card_singleton]
      norm_num
      simp only [Finset.singleton_subset_iff, ha]
    intro b hb
    rw [Finset.sum_const, Finset.card_sdiff, Finset.card_sdiff, Finset.card_range, Finset.card_singleton, Finset.card_singleton]
    norm_num
    simp only [Finset.singleton_subset_iff, ha]
    simp only [Finset.singleton_subset_iff, hb]
  -- altogether, we can relate the summation to the cardinility of the set.
  -- first instead of summing the elements in x, let us count half their value twice
  conv_lhs =>
    arg 1
    ext x
    arg 1
    ext hx
    rw [(by linarith : x = (x / 2) + x / 2)]
  rw [finsum_mem_add_distrib hSFinite]
  -- and for one of the copies, consider it to be the image under one of the bijections
  -- and for the other, consider it to be the image under the other bijection
  -- putting them back together, we have ended up summing by pairs of elements and their complements, and then halving them
  -- hence the sum is just half the cardinality of the set of triples of distinct digits,
  -- which is just $720/2=360$.
  conv_lhs =>
    congr
    · rw [← Set.SurjOn.image_eq_of_mapsTo hfT.2.2 hfT.1]
    · rw [← Set.SurjOn.image_eq_of_mapsTo hgT.2.2 hgT.1]
  simp_rw [finsum_mem_image hfT.2.1, finsum_mem_image hgT.2.1, Finset.mem_coe, finsum_mem_finset_eq_sum, ← Finset.sum_add_distrib, ← add_div, ← Finset.sum_div, Finset.sum_congr _ hfg, Finset.sum_const, hTcard]
  norm_num
