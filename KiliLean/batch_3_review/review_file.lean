import Mathlib

/- Assume that $x1,x2,…,x7$​ are real numbers such that
\begin{align*}
x_1 + 4x_2 + 9x_3 + 16x_4 + 25x_5 + 36x_6 + 49x_7 &= 1,\\
4x_1 + 9x_2 + 16x_3 + 25x_4 + 36x_5 + 49x_6 + 64x_7 &= 12,\\
9x_1 + 16x_2 + 25x_3 + 36x_4 + 49x_5 + 64x_6 + 81x_7 &= 123.
\end{align*}

Find the value of $16x_1+25x_2+36x_3+49x_4+64x_5+81x_6+100x_7$. -/
theorem algebra_95544 (x : Fin 7 → ℝ)
    (h1 : x 0 + 4 * x 1 + 9 * x 2 + 16 * x 3 + 25 * x 4 + 36 * x 5 + 49 * x 6 = 1)
    (h2 : 4 * x 0 + 9 * x 1 + 16 * x 2 + 25 * x 3 + 36 * x 4 + 49 * x 5 + 64 * x 6 = 12)
    (h3 : 9 * x 0 + 16 * x 1 + 25 * x 2 + 36 * x 3 + 49 * x 4 + 64 * x 5 + 81 * x 6 = 123) :
    16 * x 0 + 25 * x 1 + 36 * x 2 + 49 * x 3 + 64 * x 4 + 81 * x 5 + 100 * x 6 = 334 := by
  -- Define an auxiliary function `f` as follows:
  set f : ℝ → ℝ := fun k ↦ k^2 * x 0 + (k + 1)^2 * x 1 + (k + 2)^2 * x 2 + (k + 3)^2 * x 3 + (k + 4)^2 * x 4 + (k + 5)^2 * x 5 + (k + 6)^2 * x 6
    with f_def
  -- Then the hypotheses can be rewritten as giving us the following values of `f`:
  have hf1 : f 1 = 1 := by rw [f_def]; norm_num; exact h1
  have hf2 : f 2 = 12 := by rw [f_def]; norm_num; exact h2
  have hf3 : f 3 = 123 := by rw [f_def]; norm_num; exact h3
  -- The claim is equivalent to computing `f 4`:
  suffices h : f 4 = 334 by rw [f_def] at h; norm_num at h; exact h
  -- Then there are coefficients `a, b, c` such that `f k = k^2 * a + k * b + c`:
  have : ∃ a b c : ℝ, ∀ k, f k = k^2 * a + k * b + c := by
    use x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6
    use x 1 * 2 + x 2 * 4 + x 3 * 6 + x 4 * 8 + x 5 * 10 + x 6 * 12
    use x 1 + x 2 * 4 + x 3 * 9 + x 4 * 16 + x 5 * 25 + x 6 * 36
    intro k
    ring
  rcases this with  ⟨a,b,c, h⟩
  -- From the three values of `f` obtained above we get linear equations for `a, b, c`:
  have hl1 : a + b + c = 1 := by rw [← hf1, h 1]; linarith
  have hl2 : 4 * a + 2 * b + c = 12 := by rw [← hf2, h 2]; linarith
  have hl3 : 9 * a + 3 * b + c = 123 := by rw [← hf3, h 3]; linarith
  -- Solving this system of three linear equations we obtain
  have ha : a = 50 := by linarith
  have hb : b = -139 := by linarith
  have hc : c = 90 := by linarith
  -- Therefore `f 4 = 16 * a + 4 * b + c = 334` as claimed
  rw [h 4, ha, hb, hc]
  norm_num