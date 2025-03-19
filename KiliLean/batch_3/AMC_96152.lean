import Mathlib

/-
The fraction
\[\dfrac1{99^2}=0.\overline{b_{n-1}b_{n-2}\ldots b_2b_1b_0},\]
where $n$ is the length of the period of the repeating decimal expansion. What is the sum $b_0+b_1+\cdots+b_{n-1}$?

$\textbf{(A) }874\qquad \textbf{(B) }883\qquad \textbf{(C) }887\qquad \textbf{(D) }891\qquad \textbf{(E) }892\qquad$
-/
theorem number_theory_96152 : ∃ n, IsLeast { n | ∀ k, ⌊ 10 ^ n * (1 / (99:ℝ) ^ 2) ⌋ = ⌊10 ^ (n * k) * (1 / (99:ℝ) ^ 2) ⌋ } n ∧ \ := by sorry
