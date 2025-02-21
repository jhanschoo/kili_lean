import Mathlib

/--
PROBLEM:
Find the smallest prime that is the fifth term of an increasing [arithmetic sequence](https://artofproblemsolving.com/wiki/index.php/Arithmetic_sequence), all four preceding terms also being [prime](https://artofproblemsolving.com/wiki/index.php/Prime_number).
-/
theorem number_theory_709
  (P : ℕ → Prop)
  (hP : ∀ n4, P n4 ↔
    ∃ (a c : ℕ) (f : ℕ → ℕ), (c > 0) ∧ (∀ i, f i = a + c * i) ∧ Nat.Prime (f 0) ∧ Nat.Prime (f 1) ∧ Nat.Prime (f 2) ∧ Nat.Prime (f 3) ∧ Nat.Prime (f 4) ∧ f 4 = n4) :
  IsLeast { x : ℕ | P x } 29 := by
  constructor <;> simp [lowerBounds]
  · rw [hP]
    use 5, 6, (λ i => 5 + 6 * i)
    constructor
    · norm_num
    constructor
    · intro i; rfl
    norm_num
  · intro x
    intro hPx
    rw [hP] at hPx
    rcases hPx with ⟨a, c, f, hcpos, hf, hf0, hf1, hf2, hf3, hf4, hx⟩
    have hmonof (i j : ℕ) (hij : i < j) : f i < f j := by
      rw [hf, hf]
      have : c * i < c * j := Nat.mul_lt_mul_of_pos_left hij hcpos
      exact Nat.add_lt_add_left this a
    have hpdvd (d i j : ℕ) (iltj : i < j) (dgt1 : d ≠ 1) (ddvdfi : f i ≡ 0 [MOD d]) (ddvdfj : f j ≡ 0 [MOD d]): ¬Nat.Prime (f j) := by
      rw [Nat.modEq_zero_iff_dvd] at ddvdfj ddvdfi
      intro contra
      rw [Nat.dvd_prime contra] at ddvdfj
      rcases ddvdfj with ddvdfj | ddvdfj
      · contradiction
      rw [ddvdfj] at ddvdfi
      apply Nat.le_of_dvd at ddvdfi
      rw [hf, hf] at ddvdfi
      have : c * j ≤ c * i := by exact Nat.le_of_add_le_add_left ddvdfi
      have : j ≤ i := by exact Nat.le_of_mul_le_mul_left this hcpos
      linarith
      apply lt_of_lt_of_le (Nat.Prime.pos hf0)
      rw [hf, hf]
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      linarith
    -- The common difference $c$ must be even, otherwise we encounter several distinct multiples of $2$ in the part of the arithmetic sequence that must be all primes; and not all of them can be the prime number $2$. We prove this by exhaustion of c modulo 2 and a modulo 2.
    have h2dvdc : 2 ∣ c := by
      rw [← Nat.modEq_zero_iff_dvd]
      mod_cases hcmod2 : c % 2
      · exact hcmod2
      · mod_cases hamod2 : a % 2
        · have h2dvdf0 : f 0 ≡ 0 [MOD 2] := by rw [hf]; simpa
          have h2dvdf2 : f 2 ≡ 0 [MOD 2] := by
            calc
              f 2 = a + c * 2 := by rw [hf]
              _ ≡ 0 + 1 * 2 [MOD 2] := Nat.ModEq.add hamod2 (Nat.ModEq.mul hcmod2 rfl)
              _ ≡ 0 [MOD 2] := rfl
          have := hpdvd 2 0 2 (by norm_num) (by norm_num) h2dvdf0 h2dvdf2
          contradiction
        · have h2dvdf1 : f 1 ≡ 0 [MOD 2] := by
            calc
              f 1 = a + c * 1 := by rw [hf]
              _ ≡ 1 + 1 * 1 [MOD 2] := Nat.ModEq.add hamod2 (Nat.ModEq.mul hcmod2 rfl)
              _ ≡ 0 [MOD 2] := rfl
          have h2dvdf3 : f 3 ≡ 0 [MOD 2] := by
            calc
              f 3 = a + c * 3 := by rw [hf]
              _ ≡ 1 + 1 * 3 [MOD 2] := Nat.ModEq.add hamod2 (Nat.ModEq.mul hcmod2 rfl)
              _ ≡ 0 [MOD 2] := rfl
          have := hpdvd 2 1 3 (by norm_num) (by norm_num) h2dvdf1 h2dvdf3
          contradiction
    -- Similarly, the common difference $c$ must be a multiple of $3$, otherwise, except for a special case, we encounter several distinct multiples of $2$ in the part of the arithmetic sequence that must be all primes; and not all of them can be the prime number $3$. We prove this by exhaustion of c modulo 3 and a modulo 3.
    have h3dvdc : 3 ∣ c := by
      rw [← Nat.modEq_zero_iff_dvd]
      mod_cases hcmod3 : c % 3
      · exact hcmod3
      · mod_cases hamod3 : a % 3
        · have h3dvdf0 : f 0 ≡ 0 [MOD 3] := by rw [hf]; simpa
          have h3dvdf3 : f 3 ≡ 0 [MOD 3] := by
            calc
              f 3 = a + c * 3 := by rw [hf]
              _ ≡ 0 + 1 * 3 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          have := hpdvd 3 0 3 (by norm_num) (by norm_num) h3dvdf0 h3dvdf3
          contradiction
        · -- As for the special case, we have the third term of the arithmetic sequence being multiple of $3$; for it to be prime, it must be $3$ itself, in which case only one of the previous terms may be prime (and be the only smaller prime $2$), but this contradicts a hypothesis of ours that the first two terms are also prime.
          have h3dvdf2 : f 2 ≡ 0 [MOD 3] := by
            calc
              f 2 = a + c * 2 := by rw [hf]
              _ ≡ 1 + 1 * 2 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          rw [Nat.modEq_zero_iff_dvd] at h3dvdf2
          rw [Nat.dvd_prime hf2] at h3dvdf2
          rcases h3dvdf2 with h3dvdf2 | h3dvdf2
          · norm_num at h3dvdf2
          have hf0ltf1 := hmonof 0 1 (by norm_num)
          have hf1ltf2 := hmonof 1 2 (by norm_num)
          rw [← h3dvdf2] at hf1ltf2
          have : f 1 = 2 := by
            set f1 := f 1
            interval_cases f1 <;> norm_num at hf1 ; rfl
          rw [this] at hf0ltf1
          set f0 := f 0
          interval_cases f0 <;> norm_num at hf0
        · have h3dvdf1 : f 1 ≡ 0 [MOD 3] := by
            calc
              f 1 = a + c * 1 := by rw [hf]
              _ ≡ 2 + 1 * 1 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          have h3dvdf4 : f 4 ≡ 0 [MOD 3] := by
            calc
              f 4 = a + c * 4 := by rw [hf]
              _ ≡ 2 + 1 * 4 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          have := hpdvd 3 1 4 (by norm_num) (by norm_num) h3dvdf1 h3dvdf4
          contradiction
      · mod_cases hamod3 : a % 3
        · have h3dvdf0 : f 0 ≡ 0 [MOD 3] := by
            calc
              f 0 = a + c * 0 := by rw [hf]
              _ ≡ 0 + 2 * 0 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          have h3dvdf3 : f 3 ≡ 0 [MOD 3] := by
            calc
              f 3 = a + c * 3 := by rw [hf]
              _ ≡ 0 + 2 * 3 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          have := hpdvd 3 0 3 (by norm_num) (by norm_num) h3dvdf0 h3dvdf3
          contradiction
        · have h3dvdf1 : f 1 ≡ 0 [MOD 3] := by
            calc
              f 1 = a + c * 1 := by rw [hf]
              _ ≡ 1 + 2 * 1 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          have h3dvdf4 : f 4 ≡ 0 [MOD 3] := by
            calc
              f 4 = a + c * 4 := by rw [hf]
              _ ≡ 1 + 2 * 4 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          have := hpdvd 3 1 4 (by norm_num) (by norm_num) h3dvdf1 h3dvdf4
          contradiction
        · -- We encounter the special case here as well; we have the third term of the arithmetic sequence being multiple of $3$; for it to be prime, it must be $3$ itself, in which case only one of the previous terms may be prime (and be the only smaller prime $2$), but this contradicts a hypothesis of ours that the first two terms are also prime.
          have h3dvdf2 : f 2 ≡ 0 [MOD 3] := by
            calc
              f 2 = a + c * 2 := by rw [hf]
              _ ≡ 2 + 2 * 2 [MOD 3] := Nat.ModEq.add hamod3 (Nat.ModEq.mul hcmod3 rfl)
              _ ≡ 0 [MOD 3] := rfl
          rw [Nat.modEq_zero_iff_dvd] at h3dvdf2
          rw [Nat.dvd_prime hf2] at h3dvdf2
          rcases h3dvdf2 with h3dvdf2 | h3dvdf2
          · norm_num at h3dvdf2
          have hf0ltf1 := hmonof 0 1 (by norm_num)
          have hf1ltf2 := hmonof 1 2 (by norm_num)
          rw [← h3dvdf2] at hf1ltf2
          have : f 1 = 2 := by
            set f1 := f 1
            interval_cases f1 <;> norm_num at hf1 ; rfl
          rw [this] at hf0ltf1
          set f0 := f 0
          interval_cases f0 <;> norm_num at hf0
    -- Together, we have that $c$ is a multiple of $6$.
    have h5dvdc : 6 ∣ c := by
      have : (2).lcm 3 ∣ c := by exact Nat.lcm_dvd h2dvdc h3dvdc
      rw [Nat.Coprime.lcm_eq_mul (by norm_num)] at this
      exact this
    -- Assuming that $c$ is indeed $6$, we exhaust the possible values of $a$ in hopes of finding one such that the hypotheses are satisfied.
    by_cases hc6 : c = 6
    · subst hc6
      symm at hx
      subst hx
      rw [hf] at hf0 hf1 hf2 hf3 hf4 ⊢
      by_cases ha5 : 5 ≤ a
      · calc
          29 = 5 + 6 * 4 := by norm_num
          _ ≤ a + 6 * 4 := by linarith
      · simp at ha5
        interval_cases a <;> norm_num at hf0 hf1 hf2 hf3 hf4
    -- in case $c ≠ 6$, we have $c ≥ 12$, which immediately gives us a number greater than $29$ in the fifth term.
    · rw [dvd_def] at h5dvdc
      rcases h5dvdc with ⟨d, hd⟩
      have hdlb : 2 ≤ d := by
        by_contra contra
        simp at contra
        interval_cases d <;> simp at hd
        · linarith
        · contradiction
      calc
        29 ≤ 24 * d := by linarith
        _ = c * 4 := by rw [hd]; ring
        _ ≤ a + c * 4 := by linarith
        _ = f 4 := by rw [hf]
        _ = x := hx
