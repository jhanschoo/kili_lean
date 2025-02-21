import Mathlib

/--
PROBLEM:
Find the degree measure of an angle whose complement is 25% of its supplement.
$\mathrm{(A) \ 48 } \qquad \mathrm{(B) \ 60 } \qquad \mathrm{(C) \ 75 } \qquad \mathrm{(D) \ 120 } \qquad \mathrm{(E) \ 150 }$
-/
theorem algebra_1122 (d : ℚ) (h : (90 - d) = (180 - d) / 4) : d = 60 := by linarith
