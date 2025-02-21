import Mathlib

/--
PROBLEM:
Mr. Earl E. Bird gets up every day at 8:00 AM to go to work. If he drives at an average speed of 40 miles per hour, he will be late by 3 minutes. If he drives at an average speed of 60 miles per hour, he will be early by 3 minutes. How many miles per hour does Mr. Bird need to drive to get to work exactly on time?
$\textbf{(A)}\ 45 \qquad \textbf{(B)}\ 48 \qquad \textbf{(C)}\ 50 \qquad \textbf{(D)}\ 55 \qquad \textbf{(E)}\ 58$
-/
theorem algebra_1120 (mph t d : ℚ) (hlate : 40 * (t + 3 / 60) = d) (hearly : 60 * (t - 3 / 60) = d) (hmph : mph * t = d) : mph = 48 := by
  -- From the given equations, we know that $d=\left(t+\frac{1}{20}\right)40$
  have h1 : d = (t + 1/20) * 40 := by rw [← hlate]; ring
  -- and $d=\left(t-\frac{1}{20}\right)60$.
  have h2 : d = (t - 1/20) * 60 := by rw [← hearly]; ring
  -- Setting the two equal, we have $40t+2=60t-3$
  have h3 : (t + 1/20) * 40 = (t - 1/20) * 60 := by rw [← h1, h2]
  ring_nf at h3
  -- and we find $t=\frac{1}{4}$ of an hour.
  have h4 : t = 1 / 4 := by linarith
  --  Substituting t back in, we find $d=12$.
  subst t
  ring_nf at *
  -- From $d=rt$, we find that $r$, our answer, is $\boxed{\textbf{(B) }48 }$.
  subst d
  calc
    mph = 4 * (mph * (1 / 4)) := by ring
    _ = 4 * 12 := by rw [h1]
    _ = 48 := by norm_num

