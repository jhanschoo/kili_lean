import Mathlib

/--
The set $\{3,6,9,10\}$ is augmented by a fifth element $n$, not equal to any of the other four. The median of the resulting set is equal to its mean. What is the sum of all possible values of $n$?
-/
theorem AMC_Algebra_1179 : ∃ (S : Finset ℕ), ∀ n, n ∈ S ↔ n ≠ 3 ∧ n ≠ 6 ∧ n ≠ 9 ∧ n ≠ 10 ∧ 5 * (List.argmin (fun e ↦ List.sum (List.map (fun t ↦ Nat.dist e t) [3, 6, 9, 10, n])) [3, 6, 9, 10, n]).getD 0 = List.sum [3, 6, 9, 10, n] := by
  sorry
