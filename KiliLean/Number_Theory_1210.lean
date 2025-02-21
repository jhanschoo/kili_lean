import Mathlib

/--
PROBLEM:
Kiana has two older twin brothers. The product of their three ages is 128.  What is the sum of their three ages?
-/
theorem number_theory_1210 (kiana brother : ℕ) (holder : kiana < brother) (hprod : kiana * brother * brother = 128) : kiana + brother + brother = 18 := by
  rw [mul_assoc] at hprod
  --  The twins could be $2^0 = 1, 2^1 = 2, 2^2 = 4, 2^3 = 8$ years of age
  -- Just by considering the divisors of $128$, we know that the twis have age $2$ raised to some power less than $7$.
  have : ∃ (b : ℕ), b ≤ 7 ∧ brother = 2 ^ b := by
    rw [← Nat.dvd_prime_pow Nat.prime_two]
    simp
    rw [← hprod, ← mul_assoc]
    exact Nat.dvd_mul_left _ _
  rcases this with ⟨b, hb, rfl⟩
  -- We also know that Kiana is not 0 years old, since the product of their ages is positive.
  have kiana_pos : 0 < kiana := by
    contrapose! hprod
    simp at hprod
    subst hprod
    simp
  -- Now considering the magnitude of the ages of the older brothers, we obtain a better bound that $b ≤ 3$.
  have : b ≤ 3 := by
    -- This is because on the one hand that the square of $2^b$ is less than $128$.
    have : 2 ^ (b * 2) ≤ 2 ^ 7 := by
      calc
        2 ^ (b * 2) = (2 ^ b) ^ 2 := by rw [Nat.pow_mul]
        _ = 2 ^ b * 2 ^ b := by rw [Nat.pow_two]
        _ ≤ kiana * (2 ^ b * 2 ^ b) := Nat.le_mul_of_pos_left _ kiana_pos
        _ = 128 := hprod
        _ = 2 ^ 7 := by simp
    -- and then on the other hand that the square of $2^b$ is $2$ ralsied to an even power, so the power can't be $7$.
    have : b * 2 ≤ 7 := by rwa [Nat.pow_le_pow_iff_right (by norm_num)] at this
    have :
