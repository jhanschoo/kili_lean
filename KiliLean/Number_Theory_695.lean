import Mathlib

/--
PROBLEM:
Let $S$ be a list of positive integers--not necessarily distinct--in which the number $68$ appears. The average (arithmetic mean) of the numbers in $S$ is $56$. However, if $68$ is removed, the average of the remaining numbers drops to $55$. What is the largest number that can appear in $S$?
-/
theorem number_theory_695 :
  ∀ (S : Finset ℤ), (∀ x ∈ S, 0 < x ∧ x ≤ 15) →
  (∀ (T U : Finset ℤ), T ⊆ S -> U ⊆ S -> T ∩ U = ∅ ->
  ∑ i ∈ T, i ≠ ∑ j ∈ U, j) →
  (∑ x ∈ S, x) ≤ 61 := by
  intro S hdisjoint h
  have hcard : (∑ x ∈ S, x) > 61 -> S.card > 4 := by
    have : ∀ (n : ℕ), ∀ (A : Finset ℕ), (n = A.card ∧ ∀ x ∈ A, 0 < x ∧ x ≤ 15) →
      (∑ x ∈ A, x) ≤ (A.card : ℤ) * 15 - ((A.card : ℤ) * ((A.card : ℤ) - 1)) / 2 := by
      intro n
      induction' n with n ih
      · intro A ⟨hcard, hx⟩
        rw [← hcard]
        symm at hcard
        apply Finset.card_eq_zero.mp at hcard
        rw [hcard]
        norm_num
      · intro A ⟨hcard, hx⟩
