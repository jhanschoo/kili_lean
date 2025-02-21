import Mathlib

/--
PROBLEM:
A 100 foot long moving walkway moves at a constant rate of 6 feet per second.  Al steps onto the start of the walkway and stands.  Bob steps onto the start of the walkway two seconds later and strolls forward along the walkway at a constant rate of 4 feet per second.  Two seconds after that, Cy reaches the start of the walkway and walks briskly forward beside the walkway at a constant rate of 8 feet per second.  At a certain time, one of these three persons is exactly halfway between the other two.  At that time, find the distance in feet between the start of the walkway and the middle person.
-/
theorem AIME_Calculus_731
  (a b c : ℚ → ℚ)
  (ha : ∀ t, a t = 6 * t)
  (hb : ∀ t, b t = (6 + 4) * (t - 2))
  (hc : ∀ t, c t = 8 * (t - 2 - 2))
  (s : ℚ)
  (hstartwalk : 0 ≤ a s ∧ 0 ≤ b s ∧ 0 ≤ c s)
  (hendwalk : a s ≤ 100 ∧ b s ≤ 100 ∧ c s ≤ 100)
  (hmidway : 3 * a s = a s + b s + c s ∨ 3 * b s = a s + b s + c s ∨ 3 * c s = a s + b s + c s): (a s + b s + c s) / 3 = 52 := by
  simp [ha, hb, hc] at hmidway ⊢
  ring_nf at hmidway
  rcases hmidway with (hmid | hmid | hmid)
  · -- assume that Al is halfway between Bob and Cy
    -- this gives us $s = \frac{26}{3}$
    have := calc
      s = ((-52 + s * 24) - s * 18 + 52) / 6 := by ring
      _ = (s * 18 - s * 18 + 52) / 6 := by rw [hmid]
      _ = 26 / 3 := by ring_nf
    subst s
    ring
  · -- assume that Bob is halfway between Al and Cy
    -- this gives us $s = \frac{4}{3}$
    have := calc
      s = ((-60 + s * 30)  - 24 * s + 60) / 6 := by ring
      _ = ((-52 + s * 24) - 24 * s + 60) / 6 := by rw [hmid]
      _ = 4 / 3 := by ring
    subst s
    -- which can be disregarded since both Bob and Cy hadn't started yet
    rw [ha, hb, hc] at hstartwalk
    linarith
  · -- assume that Cy is halfway between Al and Bob
    -- but we obtain a contradiction with -96 = -52
    have := calc
      -96 = (-96 + s * 24) - s * 24 := by ring
      _ = (-52 + s * 24) - s * 24 := by rw [hmid]
      _ = -52 := by ring
    linarith
