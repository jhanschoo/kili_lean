import Mathlib

/--
PROBLEM:
Find the degree measure of an angle whose complement is 25% of its supplement.
$\mathrm{(A) \ 48 } \qquad \mathrm{(B) \ 60 } \qquad \mathrm{(C) \ 75 } \qquad \mathrm{(D) \ 120 } \qquad \mathrm{(E) \ 150 }$
-/
theorem algebra_1122 (x xcomplement xsupplement : ℚ) (hxcomplement : xcomplement = 90 - x) (hxsupplement : xsupplement = 180 - x) (h : xcomplement = xsupplement / 4) : x = 60 := by
  -- We can create an equation for the question, $4(90-x)=(180-x)$
  have : 4 * (90 - x) = 180 - x := by rw [← hxcomplement,← hxsupplement, h]; ring
  -- $360-4x=180-x$
  have : 360 -  4 * x = 180 - x :=
    calc
      360 - 4 * x = 4 * (90 - x) := by ring
      _ = 180 - x := by assumption
  -- $3x=180$
  have : 3 * x = 180 := by
    calc
      3 * x = (180 - x) + 4 * x - 180 := by ring
      _ = (360 - 4 * x) + 4 * x - 180 := by rw [this]
      _ = 180 := by ring
  -- After simplifying, we get $x=60 \Rightarrow \mathrm {(B)}$
  have : x = 60 := by
    calc
      x = 3 * x / 3 := by ring
      _ = 180 / 3 := by rw [this]
      _ = 60 := by norm_num
  assumption
