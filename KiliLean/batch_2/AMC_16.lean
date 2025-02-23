import Mathlib

set_option maxHeartbeats 800000

-- open List

/- Sally has five red cards numbered $1$ through $5$ and four blue cards numbered $3$ through $6$. She stacks the cards so that the colors alternate and so that the number on each red card divides evenly into the number on each neighboring blue card. What is the sum of the numbers on the middle three cards?

$\mathrm{(A) \ } 8\qquad \mathrm{(B) \ } 9\qquad \mathrm{(C) \ } 10\qquad \mathrm{(D) \ } 11\qquad \mathrm{(E) \ } 12$ -/
theorem AMC_16 (r b : List ℕ)
    (hrl : r.length = 5)
    (hrv : ∀ n, 1 ≤ n ∧ n ≤ 5 → ∃ (i : Fin 5), r[i] = n)
    (hrv' : ∀ (i : Fin 5), 1 ≤ r[i] ∧ r[i] ≤ 5)
    (hrnd : r.Nodup)
    (hbl : b.length = 4)
    (hbv : ∀ n, 3 ≤ n ∧ n ≤ 6 → ∃ (j : Fin 4), b[j] = n)
    (hbv' : ∀ (j : Fin 4), 3 ≤ b[j] ∧ b[j] ≤ 6)
    (hbnd : b.Nodup)
    (hdvd : ∀ (i : Fin 5) (j : Fin 4),
      i.val = j.val ∨ i.val = j.val + 1 → r[i] ∣ b[j]) :
    b[(1 : Fin 4)] + r[(2 : Fin 5)] + b[(2 : Fin 4)] = 12 := by
  have hrnd' {i i' : Fin 5} {v : ℕ} (hiv : r[i] = v) (hi'v : r[i'] = v) : i = i' := Fin.eq_of_val_eq ((List.Nodup.getElem_inj_iff hrnd).mp (by rw [hiv, hi'v] : r[i] = r[i']))
  have hbnd' {j j' : Fin 4} {v : ℕ} (hjv : b[j] = v) (hj'v : b[j'] = v) : j = j' := Fin.eq_of_val_eq ((List.Nodup.getElem_inj_iff hbnd).mp (by rw [hjv, hj'v] : b[j] = b[j']))
  -- Let $R_i$ and $B_j$ designate the red card numbered $i$ and the blue card numbered $j$, respectively.
  rcases hrv 1 ⟨by norm_num, by norm_num⟩ with ⟨r1, hr1⟩
  rcases hrv 2 ⟨by norm_num, by norm_num⟩ with ⟨r2, hr2⟩
  rcases hrv 3 ⟨by norm_num, by norm_num⟩ with ⟨r3, hr3⟩
  rcases hrv 4 ⟨by norm_num, by norm_num⟩ with ⟨r4, hr4⟩
  rcases hrv 5 ⟨by norm_num, by norm_num⟩ with ⟨r5, hr5⟩
  rcases hbv 3 ⟨by norm_num, by norm_num⟩ with ⟨b3, hb3⟩
  rcases hbv 4 ⟨by norm_num, by norm_num⟩ with ⟨b4, hb4⟩
  rcases hbv 5 ⟨by norm_num, by norm_num⟩ with ⟨b5, hb5⟩
  rcases hbv 6 ⟨by norm_num, by norm_num⟩ with ⟨b6, hb6⟩
  -- $B_4$ and $B_6$ are the only blue cards having the numbers that the number on $R_2$ evenly divides, so if a card is next to $R_2$, it must be $B_4$ or $B_6$.
  have hdvdr2 (j : Fin 4) (hj : r2.val = j.val ∨ r2.val = j.val + 1) : b[j] = 4 ∨ b[j] = 6 := by
    specialize hdvd _ _ hj
    rw [hr2] at hdvd
    rcases hbv' j with ⟨hbvl, hbvu⟩
    interval_cases b[j] <;> norm_cast at hdvd
  -- $B_3$ and $B_6$ are the only blue cards having the numbers that the number on $R_3$ evenly divides, so if a card is next to $R_3$, it must be $B_3$ or $B_6$.
  have hdvdr3 (j : Fin 4) (hj : r3.val = j.val ∨ r3.val = j.val + 1) : b[j] = 3 ∨ b[j] = 6 := by
    specialize hdvd _ _ hj
    rw [hr3] at hdvd
    rcases hbv' j with ⟨hbvl, hbvu⟩
    interval_cases b[j] <;> norm_cast at hdvd
  -- $B_4$ is the only blue card having the number that the number on $R_4$ evenly divides, so if a card is next to $R_4$, it must be $B_4$.
  have hdvdr4 (j : Fin 4) (hj : r4.val = j.val ∨ r4.val = j.val + 1) : b[j] = 4 := by
    specialize hdvd _ _ hj
    rw [hr4] at hdvd
    rcases hbv' j with ⟨hbvl, hbvu⟩
    interval_cases b[j] <;> norm_cast at hdvd
  -- $B_5$ is the only blue card having the number that the number on $R_5$ evenly divides, so if a card is next to $R_5$, it must be $B_5$.
  have hdvdr5 (j : Fin 4) (hj : r5.val = j.val ∨ r5.val = j.val + 1) : b[j] = 5 := by
    specialize hdvd _ _ hj
    rw [hr5] at hdvd
    rcases hbv' j with ⟨hbvl, hbvu⟩
    interval_cases b[j] <;> norm_cast at hdvd
  -- Only $R_1$, $R_2$ and $R_4$ have numbers that evenly divide the number on $B_4$, so only they can be next to $B_4$.
  have hdvdb4 (i : Fin 5) (hi : i.val = b4.val ∨ i.val = b4.val + 1) : r[i] = 1 ∨ r[i] = 2 ∨ r[i] = 4 := by
    specialize hdvd _ _ hi
    rw [hb4] at hdvd
    rcases hrv' i with ⟨hrvl, hrvu⟩
    interval_cases r[i] <;> norm_cast at hdvd
  -- Next, only $R_1$ and $R_5$ have numbers that evenly divide the number on $B_5$, so only they can be next to $B_5$.
  have hdvdb5 (i : Fin 5) (hi : i.val = b5.val ∨ i.val = b5.val + 1) : r[i] = 1 ∨ r[i] = 5 := by
    specialize hdvd _ _ hi
    rw [hb5] at hdvd
    rcases hrv' i with ⟨hrvl, hrvu⟩
    interval_cases r[i] <;> norm_cast at hdvd
  -- Next, only $R_1$, $R_2$ and $R_3$ have numbers that evenly divide the number on $B_6$, so only they can be next to $B_6$.
  have hdvdb6 (i : Fin 5) (hi : i.val = b6.val ∨ i.val = b6.val + 1) : r[i] = 1 ∨ r[i] = 2 ∨ r[i] = 3 := by
    specialize hdvd _ _ hi
    rw [hb6] at hdvd
    rcases hrv' i with ⟨hrvl, hrvu⟩
    interval_cases r[i] <;> norm_cast at hdvd
  -- We can now say that $R_5$ must be at one end of the stack
  have hr5end : r5.val = 0 ∨ r5.val = 4 := by
    rcases r5 with ⟨⟨_ | _⟩, hr5'⟩
    · left; rfl
    case mk.succ r5' =>
    simp only [Fin.getElem_fin, add_left_inj] at hr5 hdvdr5 ⊢
    by_contra! contra
    rcases contra with ⟨hc0, hc4⟩
    replace hr5v' : r5' + 1 < 4 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hr5') hc4
    set j1 : Fin 4 := ⟨r5' + 1, hr5v'⟩ with hjb
    set j0 : Fin 4 := ⟨r5', Nat.lt_of_succ_lt hr5v'⟩ with hib
    have := hbnd' (hdvdr5 j0 (by right; rfl)) (hdvdr5 j1 (by left; rfl))
    have hb : b[j0.val] = b[j1.val] := by
      rw [hdvdr5 j1 (by left; rfl), hdvdr5 j0 (by right; rfl)]
    simp only [hib, hjb, Fin.mk.injEq, self_eq_add_right, one_ne_zero] at this
  have hr5end : r5 = 0 ∨ r5 = 4 := by
    rcases hr5end with hr5end | hr5end <;> [left ; right] <;> apply Fin.eq_of_val_eq <;> rw [hr5end] <;> rfl
  -- Similarly, $R_4$ must be at one end of the stack
  have hr4end : r4.val = 0 ∨ r4.val = 4 := by
    rcases r4 with ⟨⟨_ | _⟩, hr4'⟩
    · left; rfl
    case mk.succ r4' =>
    simp only [Fin.getElem_fin, add_left_inj] at hr4 hdvdr4 ⊢
    by_contra! contra
    rcases contra with ⟨hc0, hc4⟩
    replace hr4v' : r4' + 1 < 4 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hr4') hc4
    set j1 : Fin 4 := ⟨r4' + 1, hr4v'⟩ with hjb
    set j0 : Fin 4 := ⟨r4', Nat.lt_of_succ_lt hr4v'⟩ with hib
    have := hbnd' (hdvdr4 j0 (by right; rfl)) (hdvdr4 j1 (by left; rfl))
    simp only [hib, hjb, Fin.mk.injEq, self_eq_add_right, one_ne_zero] at this
  have hr4end : r4 = 0 ∨ r4 = 4 := by
    rcases hr4end with hr4end | hr4end <;> [left ; right] <;> apply Fin.eq_of_val_eq <;> rw [hr4end] <;> rfl
  rcases hr5end with hr5end | hr5end <;> rcases hr4end with hr4end | hr4end
  · -- $R_5$ and $R_4$ cannot both be at the start of the stack
    rw [hr4end, ← hr5end, hr5] at hr4
    contradiction
  · -- Assume that $R_5$ is at the start of the stack and $R_4$ must be at the end of the stack.
    subst r5
    subst r4
    clear hr5end hr4end
    -- Then $B_5$ must follow $R_5$
    have : b[(0 : Fin 4)] = 5 := hdvdr5 (0 : Fin 4) (by left; rfl)
    have := hbnd' hb5 this
    subst b5
    -- Then $R_1$ must follow $B_5$
    have : r[(1 : Fin 5)] = 1 := by
      rcases hdvdb5 (1 : Fin 5) (by right; rfl) with h | h
      · exact h
      · have := hrnd' hr5 h
        contradiction
    have := hrnd' hr1 this
    subst r1
    -- On the other side, $B_4$ must precede $R_4$
    have : b[(3 : Fin 4)] = 4 := hdvdr4 (3 : Fin 4) (by right; rfl)
    have := hbnd' hb4 this
    subst b4
    -- Then $R_2$ must precede $B_4$
    have : r[(3 : Fin 5)] = 2 := by
      rcases hdvdb4 (3 : Fin 5) (by left; rfl) with h | h | h
      · have := hrnd' hr1 h
        contradiction
      · exact h
      · have := hrnd' hr4 h
        contradiction
    have := hrnd' hr2 this
    subst r2
    -- Then $B_6$ must precede $R_2$
    have : b[(2 : Fin 4)] = 6 := by
      rcases hdvdr2 (2 : Fin 4) (by right; rfl) with h | h
      · have := hbnd' hb4 h
        contradiction
      · exact h
    have := hbnd' hb6 this
    subst b6
    -- Then $R_3$ must precede $B_6$
    have : r[(2 : Fin 5)] = 3 := by
      rcases hdvdb6 (2 : Fin 5) (by left; rfl) with h | h | h
      · have := hrnd' hr1 h
        contradiction
      · have := hrnd' hr2 h
        contradiction
      · exact h
    have := hrnd' hr3 this
    subst r3
    -- Finally, $B_3$ must precede $R_3$
    have : b[(1 : Fin 4)] = 3 := by
      rcases hdvdr3 (1 : Fin 4) (by right; rfl) with h | h
      · exact h
      · have := hbnd' hb6 h
        contradiction
    have := hbnd' hb3 this
    subst b3
    -- The middle three cards are $B_3$, $R_3$ and $B_6$
    linarith
  · -- Assume that $R_5$ is at the end of the stack and $R_4$ is at the start of the stack. A dual situation ensues.
    subst r5
    subst r4
    clear hr5end hr4end
    -- First, $B_5$ must precede $R_5$
    have : b[(3 : Fin 4)] = 5 := hdvdr5 (3 : Fin 4) (by right; rfl)
    have := hbnd' hb5 this
    subst b5
    -- Then $R_1$ must precede $B_5$
    have : r[(3 : Fin 5)] = 1 := by
      rcases hdvdb5 (3 : Fin 5) (by left; rfl) with h | h
      · exact h
      · have := hrnd' hr5 h
        contradiction
    have := hrnd' hr1 this
    subst r1
    -- On the other side, $B_4$ must follow $R_4$
    have : b[(0 : Fin 4)] = 4 := hdvdr4 (0 : Fin 4) (by left; rfl)
    have := hbnd' hb4 this
    subst b4
    -- Then $R_2$ must follow $B_4$
    have : r[(1 : Fin 5)] = 2 := by
      rcases hdvdb4 (1 : Fin 5) (by right; rfl) with h | h | h
      · have := hrnd' hr1 h
        contradiction
      · exact h
      · have := hrnd' hr4 h
        contradiction
    have := hrnd' hr2 this
    subst r2
    -- Then $B_6$ must follow $R_2$
    have : b[(1 : Fin 4)] = 6 := by
      rcases hdvdr2 (1 : Fin 4) (by left; rfl) with h | h
      · have := hbnd' hb4 h
        contradiction
      · exact h
    have := hbnd' hb6 this
    subst b6
    -- Then $R_3$ must follow $B_6$
    have : r[(2 : Fin 5)] = 3 := by
      rcases hdvdb6 (2 : Fin 5) (by right; rfl) with h | h | h
      · have := hrnd' hr1 h
        contradiction
      · have := hrnd' hr2 h
        contradiction
      · exact h
    have := hrnd' hr3 this
    subst r3
    -- Finally, $B_3$ must follow $R_3$
    have : b[(2 : Fin 4)] = 3 := by
      rcases hdvdr3 (2 : Fin 4) (by left; rfl) with h | h
      · exact h
      · have := hbnd' hb6 h
        contradiction
    have := hbnd' hb3 this
    subst b3
    -- The middle three cards are $B_3$, $R_3$ and $B_6$
    linarith
  · -- $R_5$ and $R_4$ cannot both be at the end of the stack
    rw [hr4end, ← hr5end, hr5] at hr4
    contradiction
