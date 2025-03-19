import Mathlib

open Real Set
open scoped Real

set_option maxHeartbeats 400000

/- While finding the sine of a certain angle, an absent-minded professor failed to notice that his calculator was not in the correct angular mode. He was lucky to get the right answer. The two least positive real values of $x$ for which the sine of $x$ degrees is the same as the sine of $x$ radians are $\frac{m\pi}{n-\pi}$ and $\frac{p\pi}{q+\pi}$, where $m$, $n$, $p$, and $q$ are positive integers. Find $m+n+p+q$. -/
theorem calculus_23056 {x y : ℝ} (hxpos : 0 < x) (hypos : 0 < y)
    (hx : IsLeast {x | sin x = sin (π / 180 * x)} x)
    (hy : IsLeast {y | sin y = sin (π / 180 * y) ∧ y ≠ x} y) :
    ∃ m n p q : ℕ, 0 < m ∧ 0 < n ∧ 0 < p ∧ 0 < q ∧
    ((x = m * π / (n - π) ∧ y = p * π / (q + π)) ∨
    (y = m * π / (n - π) ∧ x = p * π / (q + π))) ∧
    m + n + p + q = 900 := by
  set sindeg := fun (x : ℝ) ↦ sin (π / 180 * x) with sindeg_def
  have sindeg_cont : Continuous sindeg := by continuity
  set s := sin - sindeg with s_def
  have s_iff (x : ℝ) : sin x = sindeg x ↔ s x = 0 := by
    dsimp [s]
    constructor <;> intro h <;> linarith
  have s_cont : Continuous s := Continuous.sub continuous_sin sindeg_cont
  have deriv_s_def : deriv s = cos - (fun x ↦ cos (π / 180 * x) * (π / 180)) := by
    ext x
    have dif_sin_id := Differentiable.comp' differentiable_sin differentiable_id
    have dif_deg_id := Differentiable.const_mul (differentiable_id : Differentiable ℝ id) (π / 180)
    have dif_sindeg_id := Differentiable.comp' differentiable_sin dif_deg_id
    rw [
      (by ext x; rfl : s = fun x ↦ (sin (id x) - sin (π / 180 * id x))),
      deriv_sub dif_sin_id.differentiableAt dif_sindeg_id.differentiableAt,
      deriv_sin differentiableAt_id,
      deriv_id,
      deriv_sin dif_deg_id.differentiableAt,
      deriv_const_mul _ differentiableAt_id,
      deriv_id,
      id_eq,
      mul_one,
      mul_one
    ]
    rfl
  -- For positive x, π / 180 * x < x
  have rads_strict_ineq (x : ℝ) (hx : 0 < x) : π / 180 * x < x := by
    nth_rw 2 [← one_mul x]
    rw [mul_lt_mul_right hx]
    linarith [pi_lt_four]

  -- We use strict monotonicity on quadrants to prove nonexistence or uniqueness of solutions
  -- sin is monotone on the first quadrant
  have sin_monoOn_1 := Real.strictMonoOn_sin
  -- sin is antitone on the second and third quadrants
  have sin_antiOn_23 : StrictAntiOn sin (Icc (π / 2) (3 * π / 2)) := by
    have : sin = sin ∘ (π + ·) ∘ (-·) := by ext x; exact (Real.sin_pi_sub x).symm
    rw [this]
    refine StrictMonoOn.comp_strictAntiOn Real.strictMonoOn_sin
      (StrictAnti.strictAntiOn (StrictAnti.const_add (StrictMono.neg strictMono_id) π) _) ?_
    simp only [MapsTo, Function.comp_apply, le_add_neg_iff_add_le, neg_add_le_iff_le_add,
      add_neg_le_iff_le_add, and_imp]
    exact (fun x ⟨hxl, hxu⟩ ↦ ⟨by linarith, by linarith⟩)
  -- sin is monotone on the fourth and fifth quadrants
  have sin_monoOn_45 : StrictMonoOn sin (Icc (3 * π / 2) (5 * π / 2)) := by
    have : sin = sin ∘ (· + -(2 * π)) := by ext x; exact (sin_sub_two_pi x).symm
    rw [this]
    refine StrictMonoOn.comp Real.strictMonoOn_sin
      (StrictMono.strictMonoOn (StrictMono.add_const strictMono_id (-(2 * π))) _) ?_
    simp only [MapsTo, le_add_neg_iff_add_le, neg_add_le_iff_le_add, add_neg_le_iff_le_add, and_imp]
    exact (fun x ⟨hxl, hxu⟩ ↦ ⟨by linarith, by linarith⟩)
  -- sindeg is monotone throughout the quadrants that we are concerned with
  have sindeg_monoOn_90 : StrictMonoOn sindeg (Icc (-90) (90)) := by
    have : sindeg = sin ∘ (π / 180 * ·) := rfl
    rw [this]
    refine StrictMonoOn.comp strictMonoOn_sin
      (StrictMono.strictMonoOn (StrictMono.const_mul strictMono_id (by linarith [pi_gt_three])) _) ?_
    simp only [MapsTo, and_imp]
    refine (fun x ⟨hxl, hxu⟩ ↦ ⟨?_, ?_⟩)
    · rw [div_mul_eq_mul_div₀, le_div_iff₀ (by linarith), ← neg_div, div_mul]
      norm_num
      rw [← div_mul, div_one, neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_left hxl (by positivity)
    · rw [le_div_iff₀ (by linarith), mul_assoc, mul_comm x, ← mul_assoc, div_mul]
      norm_num
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hxu (by positivity)
  -- hence sin - sindeg is antitone on the second and third quadrants
  have s_antiOn_1 : StrictAntiOn s (Icc (π / 2) (3 * π / 2)) := by
    rw [s_def, sub_eq_add_neg]
    refine StrictAntiOn.add sin_antiOn_23 (StrictMonoOn.neg (StrictMonoOn.mono sindeg_monoOn_90 (fun x ⟨xl, xu⟩ ↦ ⟨by linarith [pi_gt_three], by linarith [pi_lt_four]⟩)))
  -- moreover, sin - sindeg is monotone on at least the **first half** of the fifth quadrant, and we show this by bounding the derivatives. We first compute bounds on the derivatives
  have cos_antiOn_5 : StrictAntiOn cos (Icc (2 * π) (13 * π / 6)) := by
    have : cos = cos ∘ (· + -(2 * π)) := by ext x; exact (cos_sub_two_pi x).symm
    rw [this]
    refine StrictAntiOn.comp_strictMonoOn strictAntiOn_cos
      (StrictMono.strictMonoOn (StrictMono.add_const strictMono_id (-(2 * π))) _) ?_
    simp only [MapsTo, le_add_neg_iff_add_le, zero_add, add_neg_le_iff_le_add, and_imp]
    exact (fun x ⟨hxl, hxu⟩ ↦ ⟨by linarith, by linarith⟩)
  have cos_gt_5 {x : ℝ} (hx : x ∈ Ioo (2 * π) (13 * π / 6)):
      √3 / 2 < cos x := by
    rw [← cos_pi_div_six, ← cos_add_two_pi, (by ring : π / 6 + 2 * π = 13 * π / 6)]
    exact cos_antiOn_5
      (by simp at hx; exact ⟨by linarith, by linarith⟩ : x ∈ Icc (2 * π) (13 * π / 6))
      (by simp only [mem_Icc, le_refl, and_true]; linarith [pi_gt_three] : 13 * π / 6 ∈ Icc (2 * π) (13 * π / 6))
      hx.2
  -- have cosdeg_pos_on
  have deriv_s_pos_5 (x : ℝ) (hx : x ∈ interior (Icc (2 * π) (13 * π / 6))) : 0 < deriv s x := by
    rw [interior_Icc] at hx
    rw [deriv_s_def]
    specialize cos_gt_5 hx
    dsimp
    have : cos (π / 180 * x) * (π / 180) < √3 / 2 := calc
      cos (π / 180 * x) * (π / 180) ≤ 1 * (π / 180) := by rel [cos_le_one (π / 180 * x)]
      _ < √1 / 2 := by linarith [pi_lt_four, sqrt_one]
      _ < √3 / 2 := by rel [(by linarith :(1:ℝ) < 3)]
    linarith
  have s_monoOn_5 : StrictMonoOn s (Icc (2 * π) (13 * π / 6)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) (Continuous.continuousOn s_cont) deriv_s_pos_5
  -- We show that sindeg lies in (0, 1) over the quadrants we are interested in
  have sindeg_pos (x : ℝ) (hx : x ∈ Ioc 0 (5 * π / 2)) : sindeg x ∈ Ioo 0 (1/2) := by
    rcases hx with ⟨hxpos, hx5pi2⟩
    constructor
    · calc
        0 = sindeg 0 := by simp [sindeg_def]
        _ < sindeg x := by
          rwa [StrictMonoOn.lt_iff_lt sindeg_monoOn_90 (by norm_num)]
          rw [mem_Icc]
          refine ⟨by linarith, by linarith [pi_lt_four]⟩
    · calc
        sindeg x < sindeg 30 := by
          rw [StrictMonoOn.lt_iff_lt sindeg_monoOn_90 ⟨by linarith, by linarith [pi_lt_four]⟩ ⟨by linarith, by linarith⟩]
          linarith [pi_lt_four]
        _ = 1 / 2 := by
          dsimp only [sindeg]
          rw [div_mul_comm]
          norm_num
          rw [div_mul_comm, mul_one, sin_pi_div_six]

  -- First quadrant:
  -- By sin 0 = sin (π * 0 / 180) and strict monotonicity on [-π/2, π/2], the equation
  -- is not satisfied on the first quadrant x ∈ (0, π / 2].
  have hgt_q1 {x : ℝ} (hx : x ∈ Ioc 0 (π / 2)) : sin x ≠ sindeg x := by
    rcases hx with ⟨hxpos, heq⟩
    apply ne_of_gt
    rw [StrictMonoOn.lt_iff_lt sin_monoOn_1]
    exact rads_strict_ineq x hxpos
    constructor
    · exact le_trans (by linarith [pi_gt_three] : -(π / 2) ≤ 0) (by positivity)
    · rw [← one_mul (π / 2)]
      apply mul_le_mul_of_nonneg ?_ heq ?_ ?_
      all_goals linarith [pi_gt_three, pi_lt_four]
    refine ⟨?_, heq⟩
    refine le_trans ?_ (le_of_lt hxpos)
    exact le_trans (by linarith [pi_gt_three] : -(π / 2) ≤ -(3 / 2)) (by linarith)
  -- Second quadrant:
  -- By sin (π / 2) = 1, sin π = 0,
  -- against 0 < sin (π / 180 * (π / 2)) < sin (π / 180 * π) < sin (π / 180 * 90) = 1,
  -- and continuity of sin, there exists by IVT a solution to sin x = sin (π / 180 * x) in
  -- (π / 2, π). Furthermore, since sin is antitone on this interval and sin (π / 180 * · )
  -- is monotone on this interval, this solution is unique.
  have hex_q2 : ∃! x ∈ Ioo (π / 2) π, sin x = sindeg x := by
    conv in sin _ = sindeg _ => rw [s_iff]
    have hab : π / 2 ≤ π := by linarith [pi_gt_three, pi_lt_four]
    have hf : ContinuousOn s (Icc (π / 2) π) := Continuous.continuousOn s_cont
    have ivt := intermediate_value_Ioo' hab hf
    have h0 : 0 ∈ Ioo (s π) (s (π / 2)) := by
      have hpi1 := sindeg_pos π ⟨by linarith [pi_gt_three], by linarith [pi_lt_four]⟩
      have hpi2 := sindeg_pos (π / 2) ⟨by linarith [pi_gt_three], by linarith [pi_lt_four]⟩
      constructor <;> simp [s] <;> [exact hpi1.1; exact lt_trans hpi2.2 (by linarith)]
    have h0 := ivt h0
    simp only [mem_image] at h0
    rcases h0 with ⟨x0, hxI, hx2⟩
    use x0
    refine ⟨⟨hxI, by linarith⟩, (fun y ⟨hyI, hy⟩ ↦ ?_)⟩
    refine ((InjOn.eq_iff (StrictAntiOn.injOn (StrictAntiOn.mono s_antiOn_1 ?_)) hxI hyI).mp (by linarith)).symm
    intro x hx
    simp at hx ⊢
    exact ⟨by linarith, by linarith⟩
  -- Third and fourth quadrant:
  -- sin x ≤ 0 on x ∈ [π / 2, π], but 0 < sin (π / 180 * x) on the same interval due to
  -- strict monotonicity in relation to 0 = sin (π / 180 * 0). Hence there are no solutions in
  -- this half
  have hgt_q34 {x : ℝ} (hx : x ∈ Icc π (2 * π)) : sin x ≠ sindeg x := by
    simp only [mem_Icc] at hx
    refine ne_of_lt (lt_of_le_of_lt (?_ : sin x ≤ 0) ?_)
    · rw [← sin_sub_two_pi]
      apply Real.sin_nonpos_of_nonnpos_of_neg_pi_le <;> linarith
    · refine (sindeg_pos x ⟨by linarith [pi_gt_three], by linarith⟩).1
  -- Fifth quadrant:
  -- Again sin (2π) = 0, sin (5π/2) = 1,
  -- against 0 < sin (π / 180 * 2π) < sin (π / 180 * (5π/2)) < sin (π / 180 * 90) = 1,
  -- so by continuity of sin, there exists by IVT a solution to sin = sin (π / 180 * x) in
  -- (2π, 5π/2). It is harder to prove that the solution here is unique, but we do not need
  -- to do that.
  have hex_q5 : ∃! x ∈ Ioo (2 * π) (13 * π / 6), sin x = sindeg x := by
    conv in sin _ = sindeg _ => rw [s_iff]
    have hab : 2 * π ≤ 13 * π / 6 := by linarith [pi_gt_three, pi_lt_four]
    have hf : ContinuousOn s (Icc (2 * π) (13 * π / 6)) := Continuous.continuousOn s_cont
    have ivt := intermediate_value_Ioo hab hf
    have h0 : 0 ∈ Ioo (s (2 * π)) (s (13 * π / 6)) := by
      have hpi1 := sindeg_pos (2 * π) ⟨by linarith [pi_gt_three], by linarith [pi_lt_four]⟩
      have hpi2 := sindeg_pos (13 * π / 6) ⟨by linarith [pi_gt_three], by linarith [pi_lt_four]⟩
      constructor <;> simp [s] <;> [exact hpi1.1; (rw [← sin_sub_two_pi, (by ring_nf : 13 * π / 6 - 2 * π = π / 6), sin_pi_div_six]; exact hpi2.2)]
    have h0 := ivt h0
    simp only [mem_image] at h0
    rcases h0 with ⟨x0, hxI, hx2⟩
    use x0
    refine ⟨⟨hxI, by linarith⟩, (fun y ⟨hyI, hy⟩ ↦ ?_)⟩
    refine ((InjOn.eq_iff (StrictMonoOn.injOn (StrictMonoOn.mono s_monoOn_5 ?_)) hxI hyI).mp (by linarith)).symm
    intro x hx
    simp at hx ⊢
    exact ⟨by linarith, by linarith⟩

  -- We now establish that the x and y hinted at in the problem statement are exactly
  -- the ones we have found through real-analytical methods
  rcases hex_q2 with ⟨x0, ex0, ux0⟩
  rcases hex_q5 with ⟨y0, ey0, uy0⟩
  have hxx0 : x = x0 := by
    simp only [IsLeast, mem_setOf_eq, lowerBounds] at hx
    refine le_antisymm (hx.2 ex0.2) ?_
    by_cases hx1 : x ≤ π / 2
    · specialize hgt_q1 ⟨hxpos, hx1⟩
      tauto
    push_neg at hx1
    by_cases hx2 : x < π
    · linarith [ux0 x ⟨⟨hx1, hx2⟩, hx.1⟩]
    · push_neg at hx2
      linarith [ex0.1.2]
  subst x0
  have hy0x : y0 ≠ x := by
    refine ne_of_gt (lt_trans ex0.1.2 ?_)
    exact lt_trans (by linarith [pi_gt_three]) ey0.1.1
  have hyy0 : y = y0 := by
    simp only [IsLeast, mem_setOf_eq, lowerBounds, and_imp] at hy
    refine le_antisymm (hy.2 ey0.2 hy0x) ?_
    by_cases hy1 : y ≤ π / 2
    · specialize hgt_q1 ⟨hypos, hy1⟩
      tauto
    push_neg at hy1
    by_cases hy2 : y < π
    · have := ux0 y ⟨⟨hy1, hy2⟩, hy.1.1⟩
      tauto
    push_neg at hy2
    by_cases hy34 : y ≤ 2 * π
    · specialize hgt_q34 ⟨hy2, hy34⟩
      tauto
    push_neg at hy34
    by_cases hy5 : y < 13 * π / 6
    · linarith [uy0 y ⟨⟨hy34, hy5⟩, hy.1.1⟩]
    · push_neg at hy5
      linarith [ey0.1.2]
  subst y0
  -- For either solution, (π / 180 * x) lies in the 1st quadrant, and
  -- we may express x in terms of the acute (radian) angle (π / 180 * x),
  -- and this expression is unique. All the work identifying the specific
  -- quadrants that x and y lay in was in service of
  -- showing that the expressions are unique.
  -- For the first solution that sin x = sin (π / 180 * x), x is in the
  -- 2nd quadrant, so x = π - (π / 180 * x) ↔ x + (π / 180) * x = π
  --   ↔ (180 + π) / 180 * x = π ↔ x = (180 * π) / (180 + π)
  have deg_x_q1 : (π / 180 * x) ∈ Ioo 0 (π / 2) := by
    refine ⟨by positivity, ?_⟩
    cancel_denoms
    rw [mul_comm π]
    rel [lt_trans (lt_trans ex0.1.2 pi_lt_four) (by linarith : (4:ℝ) < 90)]
  have xeq : x = π - (π / 180 * x) := by
    rcases sin_eq_sin_iff.mp ex0.2 with ⟨k, hx | hx⟩
    · by_cases hk : k < 0
      · replace hk := Int.le_sub_one_iff.mpr hk
        rw [zero_sub] at hk
        rify at hk
        have := calc
          π / 180 * x = 2 * k * π + x := hx
          _ ≤ 2 * (-1) * π + x := by rel [hk]
          _ < 2 * (-1) * π + π := by rel [ex0.1.2]
          _ = -π := by ring
          _ < 0 := by linarith [pi_gt_three]
          _ < π / 180 * x := deg_x_q1.1
        linarith
      · push_neg at hk
        rify at hk
        have := calc
          π / 180 * x < π / 2 := deg_x_q1.2
          _ < x := ex0.1.1
          _ = 2 * 0 * π + x := by ring
          _ ≤ 2 * k * π + x := by rel [hk]
          _ = π / 180 * x := hx.symm
        linarith
    · rcases lt_trichotomy k 0 with hk | hk | hk
      · replace hk := Int.le_sub_one_iff.mpr hk
        rw [zero_sub] at hk
        rify at hk
        have := calc
          π / 180 * x = (2 * k + 1) * π - x := hx
          _ ≤ (2 * (-1) + 1) * π - x := by rel [hk]
          _ < (2 * (-1) + 1) * π - 0 := by rel [hxpos]
          _ = -π := by ring
          _ < 0 := by linarith [pi_gt_three]
          _ < π / 180 * x := deg_x_q1.1
        linarith
      · subst k
        linarith
      · replace hk := Int.add_one_le_iff.mpr hk
        rw [zero_add] at hk
        rify at hk
        have := calc
          π / 180 * x < π / 2 := deg_x_q1.2
          _ < 2 * π := by cancel_denoms; linarith [pi_gt_three]
          _ = (2 * 1 + 1) * π - π := by ring
          _ < (2 * 1 + 1) * π - x := by rel [ex0.1.2]
          _ ≤ (2 * k + 1) * π - x := by rel [hk]
          _ = π / 180 * x := hx.symm
        linarith
  have xeq' : x = (((180:ℕ):ℝ) * π) / (((180:ℕ):ℝ) + π) := by
    rify
    cancel_denoms at xeq
    apply add_eq_of_eq_sub at xeq
    rw [← add_mul, mul_comm] at xeq
    refine eq_div_of_mul_eq ?_ xeq
    linarith [pi_gt_three]
  -- For the 2nd solution that sin y = sin (π / 180 * y), y is in the
  -- 5nd quadrant, so y = 2 * π + (π / 180 * y) ↔ y - (π / 180) * y = 2 * π
  --   ↔ (180 - π) / 180 * y = 2 * π ↔ x = (360 * π) / (180 - π)
  have deg_y_q1 : (π / 180 * y) ∈ Ioo 0 (π / 2) := by
    refine ⟨by positivity, ?_⟩
    cancel_denoms
    rw [mul_comm π]
    have : 13 * π / 6 < 13 * 4 / 6 := by rel [pi_lt_four]
    rel [lt_trans (lt_trans ey0.1.2 this) (by linarith : (13:ℝ) * 4 / 6 < 90)]
  have yeq : y = 2 * π + (π / 180 * y) := by
    rcases sin_eq_sin_iff.mp ey0.2 with ⟨k, hy | hy⟩
    · rcases lt_trichotomy k (-1) with hk | hk | hk
      · replace hk := Int.le_sub_one_iff.mpr hk
        simp at hk
        rify at hk
        have := calc
          π / 180 * y = 2 * k * π + y := hy
          _ ≤ 2 * (-2) * π + y := by rel [hk]
          _ < 2 * (-2) * π + (13 * π / 6) := by rel [ey0.1.2]
          _ = -11/6 * π := by ring
          _ < 0 := by linarith [pi_gt_three]
          _ < π / 180 * y := deg_y_q1.1
        linarith
      · subst k
        linarith
      · replace hk := Int.add_one_le_iff.mpr hk
        simp at hk
        rify at hk
        have := calc
          π / 180 * y < π / 2 := deg_y_q1.2
          _ < 2 * π := by cancel_denoms; linarith [pi_gt_three]
          _ < y := by rel [ey0.1.1]
          _ = 2 * 0 * π + y := by ring
          _ ≤ 2 * k * π + y := by rel [hk]
          _ = π / 180 * y := hy.symm
        linarith
    · by_cases hk : k ≤ 0
      · rify at hk
        have := calc
          π / 180 * y = (2 * k + 1) * π - y := hy
          _ ≤ (2 * 0 + 1) * π - y := by rel [hk]
          _ ≤ (2 * 0 + 1) * π - 2 * π := by rel [ey0.1.1]
          _ = -π := by ring
          _ < 0 := by linarith [pi_gt_three]
          _ < π / 180 * y := deg_y_q1.1
        linarith
      · push_neg at hk
        replace hk := Int.add_one_le_iff.mpr hk
        rw [zero_add] at hk
        rify at hk
        have := calc
          π / 180 * y < π / 2 := deg_y_q1.2
          _ < 5 * π / 6 := by cancel_denoms; linarith [pi_gt_three]
          _ = (2 * 1 + 1) * π - (13 * π / 6) := by ring
          _ < (2 * 1 + 1) * π - y := by rel [ey0.1.2]
          _ ≤ (2 * k + 1) * π - y := by rel [hk]
          _ = π / 180 * y := hy.symm
        linarith
  have yeq' : y = (((360:ℕ):ℝ) * π) / (((180:ℕ):ℝ) - π) := by
    rify
    cancel_denoms at yeq
    apply sub_eq_of_eq_add at yeq
    rw [← sub_mul, mul_comm] at yeq
    refine eq_div_of_mul_eq ?_ yeq
    linarith [pi_lt_four]
  refine ⟨360, 180, 180, 180, by positivity, by positivity, by positivity, by positivity, Or.inr ⟨yeq', xeq'⟩, by norm_num⟩
