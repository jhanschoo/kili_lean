import Mathlib

/--
PROBLEM:
The mean of three numbers is $10$ more than the least of the numbers and $15$
less than the greatest. The median of the three numbers is $5$. What is their
sum?
$\textbf{(A)}\ 5\qquad \textbf{(B)}\ 20\qquad \textbf{(C)}\ 25\qquad \textbf{(D)}\ 30\qquad \textbf{(E)}\ 36$
-/
theorem algebra_1118
  (a b c : ℝ) (hmeana: (a + b + c) / 3 = a + 10) (hmeanc: (a + b + c) / 3 = c - 15) (hmedian: b = 5)
  : a + b + c = 30 := by linarith
