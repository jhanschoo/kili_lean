import Mathlib

/--
PROBLEM:
Determine the number of [ordered pairs](https://artofproblemsolving.com/wiki/index.php/Ordered_pair) $(a,b)$ of [integers](https://artofproblemsolving.com/wiki/index.php/Integer) such that $\log_a b + 6\log_b a=5, 2 \leq a \leq 2005,$ and $2 \leq b \leq 2005.$
-/
theorem algebra_729
  : { p ∈ (Finset.Icc (2 : ℕ) 2005) ×ˢ (Finset.Icc (2 : ℕ) 2005) | let (a, b) := p; Real.logb a b + 6 * Real.logb b a = 5 }.card = 54 := by
  set P : ℝ → ℝ → Prop := λ x y ↦ Real.logb x y + 6 * Real.logb y x = 5 with hP
  have H' (a b : ℕ) (haI : a ∈ (Finset.Icc (2 : ℕ) 2005)) (hbI : b ∈ (Finset.Icc (2 : ℕ) 2005)) : P a b ↔ (b:ℝ) = (a:ℝ) ^ 3 ∨ (b:ℝ) = (a:ℝ) ^ 2 := by
    rw [hP]
    simp at haI hbI ⊢
    rcases haI with ⟨ha2, _ha2005⟩
    rcases hbI with ⟨hb2, _hb2005⟩
    have h2pos : (0: ℝ) < (2: ℝ) := by positivity
    have h3pos : (0: ℝ) < (3: ℝ) := by positivity
    have hbpos : (0: ℝ) < b := by positivity
    have hapos : (0: ℝ) < a := by positivity
    have hagt1 : (1: ℝ) < a := by norm_cast
    have ha2pos : (0: ℝ) < (a:ℝ) ^ (2:ℝ) := by positivity
    have ha21 : (0: ℝ) < (a:ℝ) ^ (2:ℝ) := by positivity
    have ha2gt1 := Real.one_lt_rpow hagt1 h2pos
    have ha3gt1 := Real.one_lt_rpow hagt1 h3pos
    have hlogbpos : 0 < Real.log b := Real.log_pos (by norm_cast)
    have hlogapos : 0 < Real.log a := Real.log_pos (by norm_cast)
    have hlogabpos : 0 < Real.log a * Real.log b := mul_pos hlogapos hlogbpos
    open Real in
    constructor
      -- The equation can be rewritten as $\frac{\log b}{\log a} + 6 \frac{\log a}{\log b} = \frac{(\log b)^2+6(\log a)^2}{\log a \log b}=5$
    · intro hPab
      have :=
        calc
          (log b ^ 2 + 6 * log a ^ 2) / (log a * log b)
            = log b / log a * (log b / log b) + 6 * (log a / log b) * (log a / log a) := by ring
          _ = log b / log a + 6 * (log a / log b) := by rw [div_self (by linarith), div_self (by linarith)]; simp
          _ = logb a b + 6 * logb b a := by rw [log_div_log, log_div_log]
          _ = 5 := by rw [hPab]
      -- Multiplying through by $\log a \log b$ and factoring yields $(\log b - 3\log a)(\log b - 2\log a)=0$.
      have :=
        calc
          (log b - 3 * log a) * (log b - 2 * log a)
            = log b ^ 2 + 6 * log a ^ 2 - log a * log b * 5 := by ring
          _ = log b ^ 2 + 6 * log a ^ 2 - 5 * log a * log b := by ring
          _ = log b ^ 2 + 6 * log a ^ 2 - (log b ^ 2 + 6 * log a ^ 2) / (log a * log b) * log a * log b := by rw [this]
          _ = log b ^ 2 + 6 * log a ^ 2 - (log b ^ 2 + 6 * log a ^ 2) * ((log a * log b) / (log a * log b)) := by ring
          _ = 0 := by rw [div_self (by linarith)]; ring
      rw [mul_eq_zero] at this
      -- so either $b=a^3$ or $b=a^2$.
      rcases this with this | this
      · have :=
          calc
            log b = log b - 3 * log a + 3 * log a := by ring
            _ = 3 * log a := by rw [this]; simp
            _ = log (a ^ (3:ℝ)) := by rw [log_rpow (by positivity)]
        left
        exact Real.log_injOn_pos hbpos (by simp; positivity) (by rw [this]; norm_cast)
      · right
        have :=
          calc
            log b = log b - 2 * log a + 2 * log a := by ring
            _ = 2 * log a := by rw [this]; simp
            _ = log (a ^ (2:ℝ)) := by rw [log_rpow (by positivity)]
        exact Real.log_injOn_pos hbpos (by simp; positivity) (by rw [this]; norm_cast)
    · intro hPab
      rcases hPab with hPab | hPab <;> push_cast
      ·
        set a' := (a: ℝ) ^ (3:ℝ) with ha'
        have ha' : (a: ℝ) = a' ^ (3:ℝ)⁻¹ := by rw [ha', ← Real.rpow_mul]; simp; linarith
        rw [hPab, Real.logb_pow hapos, Real.logb_self_eq_one (by simp; linarith), ha']
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        conv_lhs => rhs; rhs; lhs; simp
        rw [Real.logb_rpow]
        ring
        positivity
        linarith
      ·
        set a' := (a: ℝ) ^ (2:ℝ) with ha'
        have ha' : (a: ℝ) = a' ^ (2:ℝ)⁻¹ := by rw [ha', ← Real.rpow_mul]; simp; linarith
        rw [hPab, Real.logb_pow hapos, Real.logb_self_eq_one (by simp; linarith), ha']
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        conv_lhs => rhs; rhs; lhs; simp
        rw [Real.logb_rpow]
        ring
        positivity
        linarith
  -- That is, the equation is equivalent to $b=a^3$ or $b=a^2$.
  have H : ∀ p ∈ (Finset.Icc (2 : ℕ) 2005) ×ˢ (Finset.Icc (2 : ℕ) 2005), (let (a, b) := p; Real.logb a b + 6 * Real.logb b a = 5) ↔ (let (a, b) := p; b = a ^ 3 ∨ b = a ^ 2) := by
    intros p hp
    rcases p with ⟨a, b⟩
    simp only [Finset.mem_product] at hp
    rcases hp with ⟨ha, hb⟩
    have := H' a b ha hb
    rw [hP] at this
    simp at this ⊢
    norm_cast at this
  rw [Finset.filter_congr H]
  -- In fact, the respective sets of ordered pairs $(a, b=a^3)$ and $(a, b=a^2)$ are disjoint for $2≤a$, so we can count them separately.
  rw [Finset.filter_or]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_filter]
    rintro ⟨a, b⟩ hp
    simp at hp ⊢
    rcases hp with ⟨⟨halb, _haub⟩, ⟨hblb, _hbub⟩⟩
    intro h
    rw [h]
    nlinarith
  )]
  set f3 : ℕ ↪ ℕ × ℕ := ⟨λ a ↦ (a, a ^ 3), by intros a b; simp⟩
  set f2 : ℕ ↪ ℕ × ℕ := ⟨λ a ↦ (a, a ^ 2), by intros a b; simp⟩
  -- The set of ordered pairs $(a, b=a^3)$ is in bijection with the set of $a$ such that $2≤a≤12$, once we consider that $b≤2005$; the latter clearly has cardinality 11.
  have h3l : { p ∈ (Finset.Icc (2 : ℕ) 2005) ×ˢ (Finset.Icc (2 : ℕ) 2005) | p.2 = p.1 ^ 3 } = Finset.map f3 (Finset.Icc (2 : ℕ) 12) := by
    ext ⟨a, b⟩
    simp [f3]
    constructor
    · intro ⟨⟨⟨halb, haub⟩, ⟨hblb, hbub⟩⟩, h3⟩
      simp [pow_succ] at h3
      subst b
      use a
      constructor <;> constructor <;> try linarith
      by_contra h
      simp at h
      apply Order.succ_le_of_lt at h
      simp at h
      nlinarith
    · intro ⟨a', ⟨⟨ha'lb, ha'ub⟩, ⟨heq,ha'b⟩⟩⟩
      subst a'
      simp [pow_succ] at ha'b ⊢
      subst b
      constructor
      constructor
      constructor
      exact ha'lb
      linarith
      constructor
      nlinarith
      nlinarith
      rfl
  rw [h3l]
  -- Similarly, the set of ordered pairs $(a, b=a^2)$ is in bijection with the set of $a$ such that $2≤a≤44$, once we consider that $b≤2005$; the latter clearly has cardinality 43.
  have h2l : { p ∈ (Finset.Icc (2 : ℕ) 2005) ×ˢ (Finset.Icc (2 : ℕ) 2005) | p.2 = p.1 ^ 2 } = Finset.map f2 (Finset.Icc (2 : ℕ) 44) := by
    ext ⟨a, b⟩
    simp [f2]
    constructor
    · intro ⟨⟨⟨halb, _haub⟩, ⟨hblb, hbub⟩⟩, h2⟩
      simp [pow_succ] at h2
      subst b
      use a
      constructor <;> constructor <;> try linarith
      by_contra h
      simp at h
      apply Order.succ_le_of_lt at h
      simp at h
      nlinarith
    · intro ⟨a', ⟨⟨ha'lb, ha'ub⟩, ⟨heq,ha'b⟩⟩⟩
      subst a'
      simp [pow_succ] at ha'b ⊢
      subst b
      constructor
      constructor
      constructor
      exact ha'lb
      linarith
      constructor
      nlinarith
      nlinarith
      rfl
  rw [h2l]
  -- So the number of ordered pairs $(a, b)$ is $11+43=54$.
  simp
