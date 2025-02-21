import Mathlib

section
theorem prime_n_factorial (n p : ℕ) (hpprime : Nat.Prime p) : p ∣ Nat.factorial n ↔ p ≤ n := by
  exact Nat.Prime.dvd_factorial hpprime
end

theorem coprime_prime_dvd_iff {n a b : ℕ} (hn : a * b = n.factorial) (hcop : a.Coprime b) {p: ℕ} (hpprime : p.Prime) (hpn : p ≤ n) : p ∣ a ↔ ¬ p ∣ b := by
  constructor
  · have := Nat.Prime.one_lt hpprime
    intro pdvda
    intro contra
    exact Nat.not_coprime_of_dvd_of_dvd this pdvda contra hcop
  · intro npdvdb
    have := (Nat.Prime.dvd_factorial hpprime).mpr hpn
    rw [← hn, Nat.Prime.dvd_mul hpprime] at this
    tauto

theorem factorial_factorization (n : ℕ) : (n.factorial).factorization = ∑ d ∈ Finset.Icc 2 n, d.factorization := by
  have factorial_prod : n.factorial = ∏ d ∈ Finset.Icc 2 n, d := by
    induction' n with n ih
    · simp
    · by_cases h : n = 0
      · subst h; simp
      · rw [Nat.factorial_succ, ih, Finset.prod_Icc_succ_top, mul_comm]
        have h : 0 < n := Nat.zero_lt_of_ne_zero h
        linarith
  calc
    n.factorial.factorization = (∏ d ∈ Finset.Ioc 1 n, d).factorization := factorial_prod ▸ rfl
    _ = ∑ d ∈ Finset.Ioc 1 n, d.factorization := by
      rw [Nat.factorization_prod]; simp; intro d hd _; linarith

theorem prime_factorization (n : ℕ) (npos : n ≠ 0) : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
  calc
    n = id n := rfl
    _ = n.factorization.prod fun (p k : ℕ) => id (p ^ k) := by
      rw [Nat.multiplicative_factorization id]
      · intro x y _; simp
      · simp
      · exact npos
    _ = n.factorization.prod fun (p k : ℕ) => (p ^ k) := by simp
    _ = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      rw [Nat.prod_factorization_eq_prod_primeFactors]


#check Nat.prod_factorization_eq_prod_primeFactors

-- theorem coprime_factors_dvd_iff (n a b : ℕ) (hn : a * b = n.factorial) (hcop : a.Coprime b) : ∃ ds ⊆ Finset.Icc 2 n, ∏ d ∈ ds, d = a ∧ ∏ d ∈ Finset.Icc 2 n \ ds, d = b := by
--   induction' n with n ih generalizing a b
--   · use ∅; simp at *; tauto
--   · by_cases hnpos : n = 0
--     · subst hnpos
--       simp at hn ⊢
--       rw [hn.1, hn.2]
--       use ∅
--       simp
--     rw [Nat.factorial_succ] at hn
--     have : n + 1 ∣ a * b := by
--       rw [hn]
--       exact Nat.dvd_mul_right (n + 1) n.factorial
--     by_cases hncop : (n + 1).Coprime b
--     · have hnpos : 0 < n := Nat.zero_lt_of_ne_zero hnpos
--       -- (n+1).Coprime b; then (n + 1) is not a factor of b.
--       apply Nat.Coprime.dvd_of_dvd_mul_right at this
--       rw [Nat.dvd_iff_div_mul_eq] at this
--       have h1 : (a / (n + 1)) * b = n.factorial := by
--         calc
--           (a / (n + 1)) * b = (a / (n + 1)) * b * (n + 1) / (n + 1) := by simp
--           _ = a / (n + 1) * (n + 1) * b / (n + 1) := by ring_nf
--           _ = a * b / (n + 1) := by rw [this]
--           _ = (n + 1) * n.factorial / (n + 1) := by rw [hn]
--           _ = n.factorial := by simp
--       have h2 : (a / (n + 1)).Coprime b := by
--         rw [← this] at hcop
--         exact Nat.Coprime.coprime_mul_right hcop
--       rcases ih (a / (n + 1)) b h1 h2 with ⟨ds, hdsI, ⟨hdsa, hdsb⟩⟩
--       use insert (n + 1) ds
--       constructor
--       · simp [(· ⊆ ·)] at hdsI ⊢
--         constructor
--         · assumption
--         · intro x hx
--           have := hdsI hx
--           omega
--       · rw [
--           ← Nat.Icc_insert_succ_right (by linarith),
--           Finset.insert_sdiff_insert,
--           Finset.sdiff_insert_of_not_mem (by simp),
--           hdsb,
--           Finset.prod_insert,
--           hdsa,
--           mul_comm,
--           this
--         ]
--         · exact ⟨rfl, rfl⟩
--         · intro contra
--           have := hdsI contra
--           simp at this
--       · exact hncop
--     · by_cases



-- theorem coprime_factor_dvd_iff (n a b : ℕ) (hn : a * b = n.factorial) (hcop : a.Coprime b) : ∃ ds ⊆ Finset.Ioc 1 n, ∏ d ∈ ds, d = a := by
--   use { d ∈ Finset.Ioc 1 n | d ∣ a }
--   simp
--   apply Nat.eq_of_factorization_eq
--   · apply ne_of_gt
--     apply Finset.prod_pos
--     simp; intro d hd _ _; positivity
--   · by_contra! contra
--     subst contra
--     simp at hn
--     linarith [Nat.factorial_pos n]
--   · intro p
--     rw [Nat.factorization_prod]
--     · sorry
--     · simp; intro d hd _ _; positivity

-- theorem coprime_factor_dvd_iff (n a b : ℕ) (hn : a * b = n.factorial) (hcop : a.Coprime b) (d : ℕ) (hdlb : 1 < d) (hdub : d ≤ n) : d ∣ a ↔ ¬d ∣ b := by
--   have facpos : 0 < n.factorial := Nat.factorial_pos n
--   have apos : 0 < a := by
--     by_contra! contra
--     simp at contra
--     subst contra
--     simp at hn
--     linarith
--   constructor
--   · have ddvdn := Nat.dvd_factorial (by linarith) hdub
--     rcases (Nat.exists_prime_and_dvd (by linarith : d ≠ 1)) with ⟨p, hpprime, pdvdd⟩
--     intro ddvda
--     have pdvda : p ∣ a := dvd_trans pdvdd ddvda
--     have advdn : a ∣ n := Nat.dvd_factorial apos ()
--     have ¬ pdvdb : ¬ p ∣ b := rw [coprime_prime_dvd_iff hn hcop hpprime]
--   · intro npdvdb
--     have := (Nat.Prime.dvd_factorial hpprime).mpr hpn
--     rw [← hn, Nat.Prime.dvd_mul hpprime] at this
--     tauto
