import Mathlib

/--
PROBLEM:
Three planets orbit a star circularly in the same plane. Each moves in the same direction and moves at constant speed. Their periods are 60, 84, and 140 years. The three planets and the star are currently collinear. What is the fewest number of years from now that they will all be collinear again?
-/
theorem AIME_Number_Theory_732
    (a b c : ℚ → ℚ)
    (ha : ∀ t, a t = t / 60)
    (hb : ∀ t, b t = t / 84)
    (hc : ∀ t, c t = t / 140) :
    IsLeast { t : ℚ | t > 0 ∧ a t ≡ b t [PMOD (1/2)] ∧ a t ≡ c t [PMOD (1/2)] } 105 := by
  -- Here, a t, b t, and c t denote the number (possibly non-integral) of complete orbits the respective stars have from their colinear starting positions. Note that this does not mean that the starting positions belong to the same half-ray from the star to planet A. But they belong to the same ray, and indeed, we are interested in whenever a planet is colinear with planet A, whether it is in the same half-ray or in the opposite half-ray. That is, whenever they are congruent modulo half a complete orbit, indicated with [PMOD (1/2)].
  conv_lhs =>
    ext x
    lhs
    ext t
    rw [ha, hb, hc]
    congr
    · rw []
    · congr
      · -- ⊢ t / 60 ≡ t / 84 [PMOD 1 / 2]
        -- We subtract t / 84 from both sides
        rw [← AddCommGroup.ModEq.sub_iff_right (by simp : t / 84 ≡ t / 84 [PMOD (1/2)])]
        tactic => ring_nf
        -- and simplify
        -- ⊢ t / 210 ≡ 0 [PMOD 1 / 2]
        rw [← AddCommGroup.zsmul_modEq_zsmul (by norm_num : (210:ℤ) ≠ 0)]
        simp
        tactic => ring_nf
        -- ⊢ t ≡ 0 [PMOD 105]
        -- This means that A and B are colinear every 105 years
      · -- ⊢ t / 60 ≡ t / 140 [PMOD 1 / 2]
        -- We subtract t / 140 from both sides
        rw [← AddCommGroup.ModEq.sub_iff_right (by simp : t / 140 ≡ t / 140 [PMOD (1/2)])]
        tactic => ring_nf
        -- and simplify
        -- ⊢ t / 105 ≡ 0 [PMOD 1 / 2]
        rw [← AddCommGroup.zsmul_modEq_zsmul (by norm_num : (210:ℤ) ≠ 0)]
        simp
        tactic => ring_nf
        -- ⊢ t * 2 ≡ 0 [PMOD 105]
        -- This means that A and B are colinear every 52.5 years
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, and_imp]
  constructor; swap
  · intro t ht h1 h2
    rcases (AddCommGroup.ModEq.symm h1) with ⟨m, hm⟩
    simp at hm
    subst hm
    norm_cast at ht ⊢
    by_cases h : 1 ≤ m <;> linarith
  · constructor
    · norm_num
    ring_nf
    conv => rhs; lhs; rw [(by simp; ring: (210:ℚ) = (2:ℤ) • 105)]
    exact ⟨AddCommGroup.self_modEq_zero, AddCommGroup.zsmul_modEq_zero 2⟩
