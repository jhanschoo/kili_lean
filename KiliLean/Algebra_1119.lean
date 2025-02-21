import Mathlib

set_option maxRecDepth 10000

/--
PROBLEM:
A charity sells $140$ benefit tickets for a total of $$2001$. Some tickets sell for full price (a whole dollar amount), and the rest sells for half price. How much money is raised by the full-price tickets?
$\textbf{(A) } \textdollar 782 \qquad \textbf{(B) } \textdollar 986 \qquad \textbf{(C) } \textdollar 1158 \qquad \textbf{(D) } \textdollar 1219 \qquad \textbf{(E) }\ \textdollar 1449$
-/
theorem algebra_1119
  (p: ℕ) (nfull : ℤ) (nhalf : ℤ) (nfullnneg : nfull ≥ 0) (nhalfnneg : nhalf ≥ 0) (hnum: nfull + nhalf = 140) (hsum : p * nfull + ((p:ℚ) / 2) * nhalf = 2001) : p * nfull = 782 := by
  -- Let's multiply ticket costs by $2$, then the half price becomes an integer, and the charity sold $140$ tickets worth a total of $4002$ dollars.
  have hsum' : 2 * (p:ℚ) * nfull + p * nhalf = 4002 := by
    calc
      2 * p * nfull + p * nhalf = 2 * (p * nfull + ((p:ℚ) / 2) * nhalf) := by ring
      _ = 4002 := by rw [hsum]; norm_num
  have hsum' : 2 * p * nfull + p * nhalf = 4002 := by norm_cast at *
  -- The cost of $140-h$ full price tickets is equal to the cost of $280-2h$ half price tickets.
  have : (140 - nhalf) * 2 * p = (280 - 2 * nhalf) * p := by ring
  -- Hence we know that $h+(280-2h) = 280-h$ half price tickets cost $4002$ dollars.
  have : (280 - nhalf) * p = 4002 :=
    calc
      (280 - nhalf) * p = nhalf * p + (280 - 2 * nhalf) * p := by ring
      _ = nhalf * p + (140 - nhalf) * 2 * p := by rw [this]
      _ = nhalf * p + nfull * 2 * p := by simp [← hnum]
      _ = 2 * p * nfull + p * nhalf := by ring
      _ = 4002 := by rw [hsum']
  -- Thus $280-h$ must be a divisor of $4002$.
  have hdvd : (280 - nhalf) ∣ 4002 := by
    rw [← this]
    exact Int.dvd_mul_right _ _
  -- we are looking for a divisor between $140$ and $280$, inclusive.
  have hlb : 140 ≤ 280 - nhalf := by linarith
  have hub : 280 - nhalf ≤ 280 := by linarith
  -- We can easily find out that the only divisor of $4002$ within the given range is $2\cdot 3\cdot 29 = 174$.
  have ht : ∃ (t : ℕ), t = 280 - nhalf := by
    use (Int.toNat (280 - nhalf))
    refine Int.toNat_of_nonneg (by linarith)
  rcases ht with ⟨t, ht⟩
  have htdvd : t ∣ 4002 := by
    have : (t:ℤ) ∣ 4002 := by rw [ht]; exact hdvd
    exact Int.ofNat_dvd.mp this
  have hlb' : 140 ≤ t := by linarith
  have hub' : t ≤ 280 := by linarith
  have htdivisors : t ∈ Nat.properDivisors 4002 := by
    rw [Nat.mem_properDivisors]
    exact ⟨htdvd, by linarith⟩
  have htdivisors' : t ∈ (Nat.properDivisors 4002).filter (λ x => 140 ≤ x ∧ x ≤ 280) := by
    rw [Finset.mem_filter]
    exact ⟨htdivisors, ⟨hlb', hub'⟩⟩
  have hpdf : (Nat.properDivisors 4002).filter (λ x => 140 ≤ x ∧ x ≤ 280) = {174} := by rfl
  rw [hpdf] at htdivisors'
  simp at htdivisors'
  rw [htdivisors'] at ht
  simp at ht
  -- hence there were $h=106$ half price tickets
  have : nhalf = 106 := by linarith
  subst this
  -- and $140-h = 34$ full price tickets.
  have : nfull = 34 := by linarith
  subst this
  -- the price of a half price ticket is $\frac{4002}{174} = 23$. Hence $23\cdot 34 = \boxed{\textbf{(A) }782}$.
  linarith
