import Mathlib

/--
PROBLEM: Diameter $AB$ of a circle has length a $2$-digit integer (base ten). Reversing the digits gives the length of the perpendicular chord $CD$. The distance from their intersection point $H$ to the center $O$ is a positive rational number. Determine the length of $AB$.
-/
theorem number_theory_691 (x y n d : ℕ) (AB CD : ℕ) (CO CH OH : ℚ) (hxI : x ∈ Finset.Icc 1 9) (hyI : y ∈ Finset.Icc 0 9) (_hcop : n.Coprime d) (hrat : OH = (n : ℚ) / d) (hOHpos : 0 < OH) (hAB : AB = 10 * x + y) (hCD : CD = 10 * y + x) (hABCO : AB = 2 * CO) (hCDCH : CD = 2 * CH) (hPyth : CH ^ 2 + OH ^ 2 = CO ^ 2) (_hAOOH : OH < CO) : 10 * x + y = 65 := by
  -- It follows that $2CO=AB=10x+y$
  have hCO : 2 * CO = 10 * x + y := by rw [← hABCO, hAB]; norm_cast
  -- and $2CH=CD=10y+x$.
  have hCH : 2 * CH = 10 * y + x := by rw [← hCDCH, hCD]; norm_cast
  -- Applying the [Pythagorean Theorem](https://artofproblemsolving.com/wiki/index.php/Pythagorean_Theorem) on $2CO$, $2OH$ and $2CH$, we deduce $(2OH)^2=\left(10x+y\right)^2-\left(10y+x\right)^2=99(x+y)(x-y)$
  have hPyth2 :=
    calc
      (2 * OH) ^ 2 = 4 * OH ^ 2 := by ring
      _ = 4 * (CO ^ 2 - CH ^ 2) := by rw [← hPyth]; ring
      _ = (2 * CO) ^ 2 - (2 * CH) ^ 2 := by ring
      _ = (10 * x + y) ^ 2 - (10 * y + x) ^ 2 := by rw [hCO, hCH]
      _ = 99 * (x + y) * (x - y) := by ring
  -- $x$ and $y$ are different digits
  by_cases hxney : x = y
  · rw [hxney] at hPyth2
    simp at hPyth2
    linarith
  -- Because $OH$ is a positive rational number and $x$ and $y$ are integral, the quantity $99(x+y)(x-y)$ must be a perfect square.
  have heq :=
    calc
      (x + y) * (x - y) * 9 * 11 = (2 * OH) ^ 2 := by rw [hPyth2]; ring
      _ = (2 * n / d) ^ 2 := by rw [hrat]; ring
  norm_cast at heq
  have : ((((2 * n : ℕ) : ℚ) / (d : ℚ)) ^ 2).den = 1 := by
    rw [← heq]
    norm_cast
  have : (((2 * n : ℕ) : ℚ) / (d : ℚ)).den = 1 := by
    rw [Rat.den_pow] at this
    rwa [pow_eq_one_iff (by norm_num)] at this
  have : ∃ (a : ℤ), a = ((2 * n : ℕ) : ℚ) / (d : ℚ) := by
    use (((2 * n : ℕ) : ℚ) / (d : ℚ)).num
    rwa [Rat.den_eq_one_iff] at this
  rcases this with ⟨a, ha⟩
  rw [← ha] at heq
  norm_cast at heq
  -- Hence either $x-y$ or $x+y$ must be a multiple of $11$Hence either $x-y$ or $x+y$ must be a multiple of $11$
  have h11prime : Prime (11 : ℤ) := by
    apply Nat.prime_iff_prime_int.mp
    norm_num
  have h11 : 11 ∣ ↑(x + y) * Int.subNatNat x y * 9 * 11 := by apply dvd_mul_left
  have h11 : 11 ∣ a := by
    apply Prime.dvd_of_dvd_pow (h11prime)
    · rw [← heq]
      exact h11
  have h121 : 11 * 11 ∣ a ^ 2 := by
    apply pow_dvd_pow_of_dvd h11
  rw [← heq] at h121
  have h11dvd : 11 ∣ ↑(x + y) * Int.subNatNat x y := by
    apply Int.dvd_of_mul_dvd_mul_right (by positivity) at h121
    apply IsCoprime.dvd_of_dvd_mul_right at h121
    · assumption
    · rw [Int.coprime_iff_nat_coprime]
      norm_num
  rw [Prime.dvd_mul h11prime] at h11dvd
  cases h11dvd
  swap
  · -- $x-y$ cannot be a multiple of 11, because both must be different digits.
    case neg.intro.inr h11dvd =>
    rw [Int.subNatNat_eq_coe] at h11dvd
    simp at hxI hyI
    rcases hxI with ⟨hx1, hx2⟩
    have : -8 ≤ (x : ℤ) - (y : ℤ) := by linarith
    have : (x : ℤ) - (y : ℤ) ≤ 9 := by linarith
    rw [dvd_iff_exists_eq_mul_left] at h11dvd
    rcases h11dvd with ⟨c, hc⟩
    rcases (lt_trichotomy c 0) with (hc' | hc' | hc')
    · have : (x - y : ℤ) ≤ -11 := by
        calc
          (x - y : ℤ) = c * 11 := by rw [hc]
          _ ≤ -1 * 11 := by apply mul_le_mul <;> linarith
          _ = -11 := by simp
      linarith
    · subst c
      simp at hc
      rw [sub_eq_zero] at hc
      norm_cast at hc
    · have : (x - y : ℤ) ≥ 11 := by
        calc
          (x - y : ℤ) = c * 11 := by rw [hc]
          _ ≥ 1 * 11 := by apply mul_le_mul <;> linarith
          _ = 11 := by simp
      linarith
  · -- Hence $x+y$ must be a multiple of $11$
    case neg.intro.inl h11dvd =>
    rw [dvd_iff_exists_eq_mul_left] at h11dvd
    rcases h11dvd with ⟨c, hc⟩
    · -- $1+0=1 \leq x+y \leq 9+9=18$, so the only possible multiple of $11$ is $11$ itself.
      have hc' : c = 1 := by
        rcases (lt_trichotomy c 1) with (hc' | hc' | hc')
        · have : ((x + y :ℕ):ℤ) ≤ 0 := by
            calc
              ((x + y : ℕ):ℤ) = c * 11 := by rw [hc]
              _ ≤ 0 * 11 := by apply mul_le_mul <;> linarith
              _ = 0 := by simp
          norm_cast at this
          simp at this hxI hyI
          linarith
        · assumption
        · have : ((x + y :ℕ):ℤ) ≥ 22 := by
            calc
              ((x + y : ℕ):ℤ) = c * 11 := by rw [hc]
              _ ≥ 2 * 11 := by apply mul_le_mul <;> linarith
              _ = 22 := by norm_num
          norm_cast at this
          simp at this hxI hyI
          linarith
      -- Therefore, $x+y$ must equal $11$
      subst c
      rw [one_mul] at hc
      rw [hc] at heq
      -- and $x-y$ must be a perfect square.
      have heq' : Int.subNatNat x y * 33 ^ 2 = a ^ 2 := by rw [← heq]; ring
      have h33dvdsq : 33 ^ 2 ∣ a ^ 2 := Dvd.intro_left _ heq'
      have h33dvd : 33 ∣ a := by
        rwa [Int.pow_dvd_pow_iff (by norm_num)] at h33dvdsq
      have h33div := Int.ediv_mul_cancel h33dvd
      rw [← h33div, mul_pow] at heq'
      apply mul_right_cancel₀ (by norm_num) at heq'
      norm_cast at hc
      rw [Int.subNatNat_eq_coe] at heq'
      set d := a / 33
      -- The only pair $(x,y)$ that satisfies this condition is $(6,5)$
      rw [← Int.natAbs_sq] at heq'
      set d' := d.natAbs
      have hdb := Int.natAbs_le_self_pow_two d'
      rw [← heq'] at hdb
      rw [sq] at heq'
      simp at hxI hyI
      rcases hxI with ⟨hx1, hx2⟩
      rcases (lt_trichotomy x 6) with (hx3 | hx3 | hx3)
      · linarith
      · linarith
      · interval_cases x
        · have hy : y = 4 := by linarith
          subst y
          norm_num at heq' hdb
          interval_cases d' <;> norm_cast at heq'
        · have hy : y = 3 := by linarith
          subst y
          norm_num at heq' hdb
          interval_cases d' <;> norm_cast at heq'
        · have hy : y = 2 := by linarith
          subst y
          norm_num at heq' hdb
          interval_cases d' <;> norm_cast at heq'
