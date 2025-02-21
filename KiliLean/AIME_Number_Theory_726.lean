import Mathlib

/--
PROBLEM:
How many positive integers have exactly three proper divisors (positive integral divisors excluding itself), each of which is less than 50?
-/
theorem AIME_Number_Theory_726
    (P : ℕ → Prop) (hP : ∀ n, P n ↔ n > 0 ∧ (∀ d ∈ n.properDivisors, d < 50) ∧ (n.properDivisors).card = 3) :
    { n : ℕ | P n }.ncard = 109 := by
  have hP' (n : ℕ) (hPn : P n) : ∃ p : ℕ, p.Prime ∧ (n = p * p * p ↔ ¬∃ q, q.Prime ∧ p ≠ q ∧ n = p * q) := by
    rw [hP n] at hPn
    rcases hPn with ⟨hPn0, hPn1, hPn2⟩
    have n_gt_one : 1 < n := by
      by_contra! h
      interval_cases n
      simp at hPn2
    sorry
  sorry
