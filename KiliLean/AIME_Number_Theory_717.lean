import Mathlib

/--
PROBLEM:
Let $N$ be the largest positive integer with the following property: reading from left to right, each pair of consecutive digits of $N$ forms a perfect square. What are the leftmost three digits of $N$?
-/
theorem AIME_Number_Theory_717 (P : ℕ → Prop)
  (hP : ∀ n, P n ↔ ∀ b, 10 ^ (b + 1) ≤ n → ∃ a, (a ^ 2 = (n / 10 ^ b) % 100) ∧ 10 ≤ a ^ 2) : ∃ n, IsGreatest { n : ℕ | P n } n ∧ ∀ b', 100 ≤ (n / 10 ^ b') ∧ (n / 10 ^ b') < 1000 → (n / 10 ^ b') = 816 := by
  -- A perfect square (that cannot be represented as a single digit) is composed of a pair of consecutive digits extracted from $n$ only if it is the square of a number between 4 and 9.
  use 81649
  simp [IsGreatest]
  constructor
  simp [upperBounds, hP]
  constructor
  swap
  · -- we first show that no smaller number satisfies the required property
    intro n hP
    -- First, define the notion of a perfect square formed by the (0-indexed) $b$-th pair of consecutive digits of $n$ counting from the right digits.
    set SqAt := fun a2 b ↦ ∃ a, a ^ 2 = a2 ∧ (a2 = (n / 10 ^ b) % 100) ∧ 10 ≤ a2 with hSqAt
    -- Note that a2 ∈ {16, 25, 36, 49, 64, 81}
    have hSqAta2 (a2 b : ℕ) (hSqAs : SqAt a2 b) : a2 = 16 ∨ a2 = 25 ∨ a2 = 36 ∨ a2 = 49 ∨ a2 = 64 ∨ a2 = 81 := by
      rcases hSqAs with ⟨a, heq, ha2n, ha2ub⟩
      have : 4 ≤ a ∧ a < 10 := by
        by_cases h : 4 ≤ a
        · by_cases h' : a < 10
          · exact ⟨h, h'⟩
          · simp at h'
            have := calc
              a ^ 2 = a2 := heq
              _ = n / 10 ^ b % 100 := ha2n
              _ < 100 := Nat.mod_lt _ (by norm_num)
              _ = 10 ^ 2 := by norm_num
              _ ≤ a ^ 2 := by rel [h']
            linarith
        · have : a ≤ 3 := by linarith
          have := calc
            a ^ 2 ≤ 3 ^ 2 := by rel [this]
            _ = 9 := by norm_num
            _ < 10 := by norm_num
          linarith
      rcases this with ⟨halb, haub⟩
      interval_cases a <;> subst heq <;> simp
    -- With this, we can characterize the required property of $n$ as follows
    have hP' (b : ℕ) (hb : 10 ^ (b + 1) ≤ n) : ∃ a2, SqAt a2 b := by
      specialize hP b hb
      rcases hP with ⟨a, ha⟩
      use a ^ 2
      simp [SqAt]
      exact ha
    -- Next, the less-significant digit of an $a2$ satisfying SqAt is exactly the digit it is extracted from
    have haux (a2 b : ℕ) (ha2 : a2 = (n / 10 ^ b) % 100) : a2 % 10 = n / 10 ^ b % 10 := by
      calc
        a2 % 10 = n / 10 ^ b % 100 % 10 := by rw [ha2]
        _ = n / 10 ^ b % 10 ^ (1 + 1) % 10 := by simp
        _ = (n / 10 ^ b % 10 ^ 1 + 10 ^ 1 * (n / 10 ^ b / 10 ^ 1 % 10)) % 10 := by rw [Nat.mod_pow_succ]
        _ = (n / 10 ^ b % 10 + 10 * (n / 10 ^ b / 10 % 10)) % 10 := by simp
        _ = n / 10 ^ b % 10 := by simp
    have hSqAsLdCongr (a2 b : ℕ) (hSqAt : SqAt a2 b) : a2 % 10 = n / 10 ^ b % 10 := by
      rcases hSqAt with ⟨a, ha2, ha2n, ha2ub⟩
      exact haux a2 b ha2n
    -- Then the more-significant digit of an $a2$ satisfying SqAt is exactly the digit it is extracted from
    have hSqAsUdCongr (a2 b : ℕ) (hSqAt : SqAt a2 b) : (a2 / 10) % 10 = n / 10 ^ (b + 1) % 10 := by sorry
    -- Together, if $n$ satisfies the required property, then it is formed of the more-significant digits of its constituent perfect squares and the less-significant digit of the smallest perfect square
    have hOfSq (f : ℕ → ℕ) (hl : ∀ b, (10 ^ (b + 1) ≤ n → SqAt (f b) b) ∧ n < 10 ^ (b + 2)) : n = (f 0) % 10 + ∑ b in Finset.range (Nat.log 10 n), (f b / 10) * 10 ^ (b + 1) := by sorry
    -- In addition, consecutive perfect squares must share their corresponding digits
    have hOverlap (b al au : ℕ) (hal : SqAt al b) (hau : SqAt au (b + 1)) : al / 10 % 10 = au % 10 := by calc
      al / 10 % 10 = n / 10 ^ (b + 1) % 10 := hSqAsUdCongr al b hal
      _ = au % 10 := (hSqAsLdCongr au (b + 1) hau).symm
    -- In particular, we have the following properties for the following specific perfect squares
    -- For 4 ^ 2 = 16, only 9 ^ 2 = 81 can precede it
    have h16 (a b : ℕ) (hal : SqAt 16 b) (hau : SqAt a (b + 1)) : a = 81 := by
      have hOver := hOverlap b 16 a hal hau
      have ha := hSqAta2 a (b + 1) hau
      rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp at hOver ⊢
    -- For 5 ^ 2 = 25, nothing can precede it
    have h25 (a b : ℕ) (hal : SqAt 25 b) : ¬ SqAt a (b + 1) := by
      intro hau
      have hOver := hOverlap b 25 a hal hau
      have ha := hSqAta2 a (b + 1) hau
      rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp at hOver
    -- For 6 ^ 2 = 36, nothing can precede it
    have h36 (a b : ℕ) (hal : SqAt 36 b) : ¬ SqAt a (b + 1) := by
      intro hau
      have hOver := hOverlap b 36 a hal hau
      have ha := hSqAta2 a (b + 1) hau
      rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp at hOver
    -- For 7 ^ 2 = 49, only 8 ^ 2 = 64 can precede it
    have h49 (a b : ℕ) (hal : SqAt 49 b) (hau : SqAt a (b + 1)) : a = 64 := by
      have hOver := hOverlap b 49 a hal hau
      have ha := hSqAta2 a (b + 1) hau
      rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp at hOver ⊢
    -- For 8 ^ 2 = 64, only 4 ^ 2 = 16 or 6 ^ 2 = 36 can precede it
    have h64 (a b : ℕ) (hal : SqAt 64 b) (hau : SqAt a (b + 1)) : a = 16 ∨ a = 36 := by
      have hOver := hOverlap b 64 a hal hau
      have ha := hSqAta2 a (b + 1) hau
      rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp at hOver ⊢
    -- For 9 ^ 2 = 81, nothing can precede it
    have h81 (a b : ℕ) (hal : SqAt 81 b) : ¬ SqAt a (b + 1) := by
      intro hau
      have hOver := hOverlap b 81 a hal hau
      have ha := hSqAta2 a (b + 1) hau
      rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp at hOver
    -- We show the impossibility of $n>81649$ satisfying the required property by contradiction
    by_contra! hn
    -- First, we show that $n$ must have at least 4 digits
    have h4dig : 10 ^ 4 ≤ n := calc
      10 ^ 4 ≤ 81649 := by norm_num
      _ ≤ n := by linarith
    -- We exhaust all cases and show impossibility for each; we must have perfect squares in at least 4 pairs of consecutive digits
    cases hP' 0 (le_trans (by norm_num) h4dig); case intro a0 ha0 =>
    cases hP' 1 (le_trans (by norm_num) h4dig); case intro a1 ha1 =>
    cases hP' 2 (le_trans (by norm_num) h4dig); case intro a2 ha2 =>
    cases hP' 3 (le_trans (by norm_num) h4dig); case intro a3 ha3 =>
    · have := hSqAta2 _ _ ha0
      rcases this with (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Starting from 16, $816$ is only two perfect squares
        have := h16 _ _ ha0 ha1
        subst this
        · exact h81 _ _ ha1 ha2
      · -- Starting from 25, $25$ is only one perfect square
        exact h25 _ _ ha0 ha1
      · -- Starting from 36, $36$ is only one perfect square
        exact h36 _ _ ha0 ha1
      · -- Starting from 49, we have $81649$ or $3649$, the answer itself; and only 3 perfect squares respectively
        have := h49 _ _ ha0 ha1
        subst this
        rcases h64 _ _ ha1 ha2 with (rfl | rfl)
        · have := h16 _ _ ha2 ha3
          subst this
          by_cases h5dig : n < 10 ^ (4 + 1)
          · -- When $n$ has 4 digits, we have $81649$ as the only solution
            -- here, hOfSq synthesizes $81649$ from its constituent perfect squares
            have hlog : Nat.log 10 n = 4 := by
              rw [Nat.log_eq_iff (by left; norm_num)]
              exact ⟨h4dig, h5dig⟩
            have := hOfSq (fun b => if b = 0 then 49 else if b = 1 then 64 else if b = 2 then 16 else 81) (by sorry)
            rw [hlog] at this
            simp at this
            rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at this
            simp at this
            linarith
          · -- If $n$ should have 5 digits, it violates that SqAt a 4 is impossible
            rw [not_lt] at h5dig
            cases hP' 4 h5dig; case neg.intro a4 ha4 =>
            exact h81 _ _ ha3 ha4
        · exact h36 _ _ ha2 ha3
      · -- Starting from 49, we have $8164$ or $364$; only 3 perfect squares and 2 perfect squares respectively
        rcases h64 _ _ ha0 ha1 with (rfl | rfl)
        · have := h16 _ _ ha1 ha2
          subst this
          exact h81 _ _ ha2 ha3
        · exact h36 _ _ ha1 ha2
      · -- Starting from 16, $81$ is only one perfect square
        exact h81 _ _ ha0 ha1
  · -- we now verify the required property on $81649$ that each pair of consecutive digits forms a perfect square
    intro b hb
    by_cases h : b < 4
    · interval_cases b
      · use 7; simp
      · use 8; simp
      · use 4; simp
      · use 9; simp
    · simp at h
      have := calc
        81649 < 100000 := by norm_num
        _ = 10 ^ (4 + 1) := by norm_num
        _ ≤ 10 ^ (b + 1) := by
          apply Nat.pow_le_pow_right (by norm_num)
          exact Nat.succ_le_succ h
        _ ≤ 81649 := hb
      linarith
  · -- finally, we compute the leftmost three digits of $81649$
    intro b hlb hub
    rcases lt_trichotomy b 2 with (hb | rfl | hb)
    · interval_cases b <;> simp at hub
    · simp
    · have hb : 3 ≤ b := by linarith
      have := calc
        100 ≤ 81649 / 10 ^ b := hlb
        _ ≤ 81649 / 10 ^ 3 := Nat.div_le_div_left (Nat.pow_le_pow_right (by positivity) hb) (by norm_num)
        _ = 81 := by norm_num
        _ < 100 := by norm_num
      linarith
