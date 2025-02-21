import Mathlib

/--
PROBLEM:
What is the largest even integer that cannot be written as the sum of two odd composite numbers?
-/

/- There is a largest even integer that cannot be written as the sum of two odd composite numbers, and it is 38. -/
theorem number_theory_693 :
  -- There exists an integer n
  ∃ (n : ℤ),
  -- that is even
  Even n ∧
  -- that cannot be written as the sum of two odd composite numbers
  ¬(∃ (a b : ℕ), Odd a ∧ ¬Nat.Prime a ∧ Odd b ∧ ¬Nat.Prime b ∧ n = a + b) ∧
  -- and is the largest such integer
  (∀ (m : ℤ),
    (Even m ∧
    ¬∃ (a b : ℕ), Odd a ∧ ¬Nat.Prime a ∧ Odd b ∧ ¬Nat.Prime b ∧ n = a + b) -> m = n) ∧
  -- and that integer is 38
  n = 38 := by
  -- The easiest method is to notice, for example, that any number that ends in a 5 is a composite (except for 5 itself).
  have hex5 : ∀ (n : ℕ), n % 10 = 5 ∧ n ≠ 5 → ¬Nat.Prime n := by
    intro n ⟨hfive, hnfive⟩
    have h2 : ∃ k, 5 + 10 * k = n := by
      use n / 10
      rw [← hfive, Nat.mod_add_div n 10]
    rcases h2 with ⟨k, hk⟩
    have hfivedvd : 5 ∣ n := by
      rw [← hk]
      apply Nat.dvd_add
      · apply Nat.dvd_refl
      · apply dvd_mul_of_dvd_left
        norm_num
    intro contra
    rw [Nat.prime_def_lt''] at contra
    rcases contra with ⟨hgt1, hndvd⟩
    specialize hndvd 5 hfivedvd
    rcases hndvd with hfiveone | hfive
    · norm_num at hfiveone
    · rw [hfive] at hnfive
      norm_num at hnfive
  -- Now consider a number can be written as the sum of two numbers, one of which ends in a 5 (the other may or may not end in a 5). Then every number greater than the considered number that ends in the same digit as the considered number itself can be written as the sum of two numbers; an odd composite number and the number we mentioned earlier that may or may not end in the 5. This comes from our previous result that any number greater than a number that ends in a 5, that also ends in a 5, is a composite odd number.
  have hgt : ∀ (n m u: ℕ), (n % 10 = m % 10 ∧ n < m ∧ ∃ (t : ℕ), t % 10 = 5 ∧ n = t + u) → ∃ (v : ℕ), Odd v ∧ ¬Nat.Prime v ∧ m = u + v := by
    intro n m u ⟨hnm, hlt, ⟨t, ht, hn⟩⟩
    have hmmod := Nat.div_add_mod m 10
    have hnmod := Nat.div_add_mod n 10
    have hnm : ∃ k, k > 0 ∧ m = n + 10 * k := by
      have : 10 * (n / 10) + n % 10 < 10 * (m / 10) + n % 10 := by
        nth_rw 2 [hnm]
        rw [Nat.div_add_mod, Nat.div_add_mod]
        exact hlt
      have div_le : n / 10 < m / 10 := by linarith
      use m / 10 - n / 10
      constructor
      · exact Nat.zero_lt_sub_of_lt div_le
      · calc
          m = 10 * (m / 10) + n % 10 := by linarith [hnm]
          _ = 10 * (n / 10 + m / 10 - n / 10) + n % 10 := by congr; rw [add_comm, Nat.add_sub_self_right]
          _ = 10 * (n / 10 + (m / 10 - n / 10)) + n % 10 := by congr; rw [Nat.add_sub_assoc (by linarith)]
          _ = n + 10 * (m / 10 - n / 10) := by linarith [Nat.div_add_mod n 10]
    rcases hnm with ⟨k, hpos, hm⟩
    use t + 10 * k
    have htkends5 : (t + 10 * k) % 10 = 5 := by
      rw [Nat.add_mul_mod_self_left, ht]
    have htkOdd : Odd (t + 10 * k) := by
      rw [Nat.odd_iff]
      calc
        (t + 10 * k) % 2 = (t + (2 * (5 * k))) % 2 := by ring_nf
        _ = t % 2 := by rw [Nat.add_mul_mod_self_left]
        _ = (10 * (t / 10) + t % 10) % 2 := by rw [Nat.div_add_mod t 10]
        _ = (t % 10 + 2 * (5 * (t / 10))) % 2 := by ring_nf
        _ = 5 % 2 := by rw [Nat.add_mul_mod_self_left, ht]
        _ = 1 := by norm_num
    constructor
    · exact htkOdd
    have htkne5 : t + 10 * k ≠ 5 := by linarith
    constructor
    · exact hex5 (t + 10 * k) ⟨htkends5, htkne5⟩
    linarith
