import Mathlib

/--
PROBLEM:
Given a [rational number](https://artofproblemsolving.com/wiki/index.php/Rational_number), write it as a [fraction](https://artofproblemsolving.com/wiki/index.php/Fraction) in lowest terms and calculate the product of the resulting [numerator](https://artofproblemsolving.com/wiki/index.php/Numerator) and [denominator](https://artofproblemsolving.com/wiki/index.php/Denominator). For how many rational numbers between $0$ and $1$ will $20_{}^{}!$ be the resulting [product](https://artofproblemsolving.com/wiki/index.php/Product)?
-/
theorem number_theory_702 : (Set.Ioo (0:ℚ) 1 ∩ {r : ℚ | r.num * r.den = (20).factorial }).ncard = 128 := by
  have prime_factorization (n : ℕ) (npos : n ≠ 0) : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
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
  set S' := fun (n : ℕ) ↦ Set.Ioo (0 : ℚ) 1 ∩ {r : ℚ | r.num * r.den = n } with hS'
  have : (Set.Ioo 0 1 ∩ {r : ℚ | r.num * r.den = (20).factorial}) = S' (20).factorial := by rw [hS']
  rw [this]
  --  If the fraction is in the form $\frac{a}{b}$, then $a < b$ and $\gcd(a,b) = 1$
  set S := fun (n : ℕ) ↦ { a ∈ Nat.divisorsAntidiagonal n | a.1 < a.2 ∧ Nat.Coprime a.1 a.2 }
  let f : ℕ × ℕ → ℚ := fun (⟨a, b⟩ : ℕ × ℕ) => Rat.divInt a b
  have hSnezero {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ S n) : p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, ne_eq, Set.mem_setOf_eq, S] at hp ⊢
    rcases hp with ⟨⟨hn, hpos⟩, hlt, hcop⟩
    by_contra contra
    simp only [not_and_or, Decidable.not_not] at contra
    rcases contra with contra | contra <;> rw [contra] at hn <;> simp at hn <;> rw [hn] at hpos <;> contradiction
  have hfinj' (n : ℕ) (p : ℕ × ℕ) (hp : p ∈ S n) : (f p).num = p.1 ∧ (f p).den = p.2 := by
    have ⟨_hpos'1, hpos'2⟩ := hSnezero hp
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, ne_eq, Set.mem_setOf_eq, S, f, Rat.den_mk, Rat.num_mk] at hp ⊢
    rcases hp with ⟨⟨_hn, _hpos⟩, _hlt, hcop⟩
    simp [hcop, Int.sign_natCast_of_ne_zero hpos'2]; tauto
  have hSBijS' (n : ℕ) : Set.BijOn f (S n) (S' n) := by
    unfold Set.BijOn
    have hInjOn : Set.InjOn f (S n) := by
      simp [Set.InjOn, S']
      intro a1 b1 h1 a2 b2 h2 heq
      have ha1 := hfinj' n (a1, b1) h1
      have ha2 := hfinj' n (a2, b2) h2
      simp at ha1 ha2
      rw [← heq, ha1.1, ha1.2] at ha2
      norm_cast at ha2
    have hSurjOn : Set.SurjOn f (S n) (S' n) := by
      simp [Set.SurjOn, S', S, f, -Rat.divInt_ofNat]
      intro q hq
      simp [-Rat.divInt_ofNat] at hq ⊢
      rcases hq with ⟨⟨hqpos, hql1⟩, hn⟩
      use q.num.natAbs, q.den
      have qnumpos : 0 < q.num := Rat.num_pos.mpr hqpos
      have qdenpos : 0 < q.den := Rat.den_pos q
      have qnumnatAbseq : q.num.natAbs = q.num := by
        cases h : q.num
        · case ofNat a => simp
        · case negSucc a => rw [h] at qnumpos; norm_num at qnumpos
      rw [← qnumnatAbseq] at hn
      constructor
      · constructor
        · norm_cast at hn
          constructor
          · exact hn
          · rw [← hn]
            positivity
        · constructor
          · have : q.num < q.den := by rwa [← Rat.lt_one_iff_num_lt_denom]
            rw [← qnumnatAbseq] at this
            norm_cast at this
          · exact q.reduced
      · rw [qnumnatAbseq]; simp
    have hMapsTo : Set.MapsTo f (S n) (S' n) := by
      simp [Set.MapsTo, S']
      intro a b hS
      have ⟨hanezero, hbnezero⟩ := hSnezero hS
      have ⟨ha, hb⟩ := hfinj' n (a, b) hS
      simp [S, f, -Rat.divInt_ofNat, -ne_eq] at hanezero hbnezero ha hb hS ⊢
      rw [← Rat.num_pos, Rat.lt_one_iff_num_lt_denom, ha, hb]
      rcases hS with ⟨⟨hn, _hpos⟩, hlt, _cop⟩
      exact ⟨⟨by positivity, by norm_cast⟩, by norm_cast⟩
    exact ⟨hMapsTo, hInjOn, hSurjOn⟩
  have (n : ℕ) := calc
    (S' n).ncard = (f '' (S n)).ncard := by
      rw [Set.BijOn.image_eq (hSBijS' n)]
    _ = (S n).card := by
      rw [Set.ncard_image_of_injOn (Set.BijOn.injOn (hSBijS' n)), Set.ncard_eq_toFinset_card']
      simp only [Finset.toFinset_coe]
  rw [this]
  -- By symmetry, to each such fraction $\frac{a}{b}$, there corresponds a fraction $\frac{b}{a}$ in lowest terms with the same a * b = 20! such that b < a; clearly the sets of these fractions are disjoint, and of equal cardinality.
  have hSSwapDisjoint (n : ℕ) : Disjoint (S n) (Prod.swap '' (S n)).toFinset := by
    simp [S]
    rw [Finset.disjoint_left]
    intro ⟨a, b⟩
    simp
    intro _ _ haltb _ a' b' _ _ ha'ltb' _ heq'
    linarith
  -- Their union is the set of fractions $\frac{a}{b}$ with the same a * b = 20!, except perhaps for a = b. But because a and b are coprime and 20! > 1, a = b is impossible; the union is thus twice the set of fractions $\frac{a}{b}$ with a < b and a * b = 20!.
  set Sb := fun (n : ℕ) ↦ { p ∈ Nat.divisorsAntidiagonal n | Nat.Coprime p.1 p.2 }
  have hSbunion (n : ℕ) (hnone : 1 < n) : S n ∪ (Prod.swap '' (S n : Set (ℕ × ℕ))).toFinset = Sb n := by
    ext ⟨a, b⟩
    simp [S, Sb]
    constructor
    · rintro (h | ⟨a', b', ⟨h, rfl, rfl⟩⟩)
      · tauto
      · rw [mul_comm, Nat.coprime_comm]; tauto
    · intro ⟨⟨hn, hpos⟩, hcop⟩
      rcases (lt_trichotomy a b) with (hlt | heq | hgt)
      · tauto
      · subst heq
        simp at hcop
        subst hcop
        simp at hn
        symm at hn
        linarith
      · right; use b, a; rw [mul_comm, Nat.coprime_comm]; tauto
  have hSSwapCard (n : ℕ) : (S n).card = (Prod.swap '' (S n : Set (ℕ × ℕ))).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Prod.swap_injective,  Set.ncard_eq_toFinset_card']
    simp
  have (n : ℕ) (hnone : 1 < n) := calc
    (Sb n).card = (S n ∪ (Prod.swap '' (S n : Set (ℕ × ℕ))).toFinset).card := by
      rw [hSbunion n hnone]
    _ = (S n).card + (Prod.swap '' (S n : Set (ℕ × ℕ))).toFinset.card := by
      rw [Finset.card_union_eq_card_add_card.mpr (hSSwapDisjoint n)]
    _ = 2 * (S n).card := by
      rw [← hSSwapCard n]; ring
  have (n : ℕ) (hnone : 1 < n) := calc
    (S n).card = 2 * (S n).card / 2 := by rw [mul_div_cancel_left₀ _ (by norm_num)]
    _ = (Sb n).card / 2 := by rw [this n hnone]
  rw [this _ (by rw [Nat.one_lt_factorial]; norm_num)]
  --  There are $2^c$ ways of selecting some [combination](https://artofproblemsolving.com/wiki/index.php/Combination) of numbers for $a$, where $c$ is the number of [prime factors](https://artofproblemsolving.com/wiki/index.php/Prime_factor) of $20!$, since each prime factor of $20!$ must be a factor of exactly one of $a$ or $b$; there are exactly as many ways of choosing the prime factors of $a$ as the number of distinct subsets of prime factors of $20!$.
  set Sb' := fun (n : ℕ) ↦ { a ∈ Nat.divisors n | Nat.Coprime a (n / a) }
  have hSbBijSb' (n : ℕ) : Set.BijOn (fun d ↦ (d, n / d)) (Sb' n) (Sb n) := by
    simp [Sb, Sb']
    constructor
    · simp [Set.MapsTo]
      intro d hd hnpos hdcop
      exact ⟨⟨Nat.mul_div_cancel_left' hd, hnpos⟩, hdcop⟩
    constructor
    · simp [Set.InjOn]
      intro d1 _ _ _ d2 _ _ _ heq _
      exact heq
    · simp [Set.SurjOn]
      intro d hd
      simp at hd ⊢
      rcases hd with ⟨⟨hn, hnpos⟩, hcop⟩
      use d.1
      nth_rw 1 [← hn]
      have hd1dvd : d.1 ∣ n := by rw [← hn]; exact dvd_mul_right d.1 d.2
      have hd1pos : d.1 ≠ 0 := ne_zero_of_dvd_ne_zero hnpos hd1dvd
      have hd2 : d.2 = n / d.1 := by rw [← hn, mul_div_cancel_left₀ d.2 hd1pos]
      have hcop : d.1.Coprime (n / d.1) := by rwa [hd2] at hcop
      have hrfl : (d.1, n / d.1) = d := by rw [← hd2]
      exact ⟨⟨⟨dvd_mul_right d.1 d.2, hnpos⟩, hcop⟩, hrfl⟩
  have (n : ℕ) : (Sb n).card = (Sb' n).card := by
    calc
      (Sb n).card = (Sb n : Set (ℕ × ℕ)).toFinset.card := by simp
      _ = (Sb n : Set (ℕ × ℕ)).ncard := by rw [Set.ncard_eq_toFinset_card']
      _ = ((fun d ↦ (d, n / d)) '' ((Sb' n): Set ℕ)).ncard := by rw [Set.BijOn.image_eq (hSbBijSb' n)]
      _ = ((Sb' n): Set ℕ).ncard := by rw [Set.ncard_image_of_injOn (Set.BijOn.injOn (hSbBijSb' n))]
      _ = (Sb' n : Set ℕ).toFinset.card := by rw [Set.ncard_eq_toFinset_card']
      _ = (Sb' n).card := by simp
  rw [this]
  set g := fun (n : ℕ) (ds : Finset ℕ) ↦ ∏ p ∈ ds, p ^ (n.factorization p)
  have hpFBijSb' (n : ℕ) (hnnone : 1 < n) : Set.BijOn (g n) (n.primeFactors.powerset) (Sb' n) := by
    have hinj' : ∀ x1 ∈ n.primeFactors.powerset, ∀ x2 ∈ n.primeFactors.powerset, g n x1 = g n x2 → x1 ⊆ x2 := by
      intro x1 hx1pF x2 hx2pF heq
      simp [g] at hx1pF hx2pF heq
      intro p hpx1
      have hppF := hx1pF hpx1
      have hpprime := Nat.prime_of_mem_primeFactors hppF
      have hpdvdLf : p ∣ ∏ p ∈ x1, p ^ n.factorization p := by
        have : p ∣ p ^ n.factorization p := dvd_pow_self p (ne_of_gt (Nat.Prime.factorization_pos_of_dvd hpprime (by positivity) (Nat.dvd_of_mem_primeFactors hppF)))
        apply Nat.dvd_trans this
        apply Finset.dvd_prod_of_mem _ hpx1
      rw [heq, Prime.dvd_finset_prod_iff (Nat.Prime.prime hpprime)] at hpdvdLf
      rcases hpdvdLf with ⟨d, hdx2, hpdvdd⟩
      have hdprime : Nat.Prime d := Nat.prime_of_mem_primeFactors (hx2pF hdx2)
      have pdvdd : p ∣ d := Nat.Prime.dvd_of_dvd_pow hpprime hpdvdd
      have : p = d := by
        rwa [prime_dvd_prime_iff_eq (Nat.Prime.prime hpprime) (Nat.Prime.prime hdprime)]   at pdvdd
      subst this
      exact hdx2
    have hInjOn : Set.InjOn (g n) (n.primeFactors.powerset) := by
      intro x1 hx1 x2 hx2 heq
      apply le_antisymm
      · exact hinj' x1 hx1 x2 hx2 heq
      · exact hinj' x2 hx2 x1 hx1 heq.symm
    have hSurjOn : Set.SurjOn (g n) (n.primeFactors.powerset) (Sb' n) := by
      simp [Sb', g]
      intro d hd
      simp at hd ⊢
      rcases hd with ⟨⟨hddvdn, hnpos⟩, hcop⟩
      have hn : n = d * (n / d) := (Nat.mul_div_cancel' hddvdn).symm
      use d.primeFactors
      have hdpos : (0 : ℕ) < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hnpos hddvdn)
      have hfcop : (fun x ↦ x ^ n.factorization x) = (fun x ↦ (fun x ↦ x ^ d.factorization x) x * (fun x ↦ x ^ (n / d).factorization x) x) := by
        funext p
        simp
        rw [hn, Nat.factorization_mul_of_coprime hcop, Finsupp.add_apply, Nat.pow_add, Nat.mul_div_cancel_left (n / d) hdpos]
      have hfcop' : ∏ x ∈ d.primeFactors, x ^ (n / d).factorization x = 1 := by
        apply Finset.prod_eq_one
        intro p hppF
        rw [Nat.factorization_eq_zero_of_not_dvd]
        · simp
        · intro contra
          have pdvdd : p ∣ d := Nat.dvd_of_mem_primeFactors hppF
          have := Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hppF)) pdvdd contra
          contradiction
      constructor
      · intro p hppF
        simp at hppF ⊢
        rcases hppF with ⟨hpprime, hpdvd, _hdpos⟩
        have hpdvdn := dvd_trans hpdvd hddvdn
        exact ⟨hpprime, hpdvdn, hnpos⟩
      · rw [hfcop, Finset.prod_mul_distrib, ← prime_factorization d (by positivity), hfcop', mul_one]
    have hMapsTo : Set.MapsTo (g n) (n.primeFactors.powerset) (Sb' n) := by
      simp [Sb', g]
      intro x hx
      simp at hx ⊢
      have hn : n = (∏ p ∈ x, p ^ n.factorization p) * ∏ p ∈ (n.primeFactors \ x), p ^ n.factorization p := by
        calc
          n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by rw [← prime_factorization n (by positivity)]
          _ = (∏ p ∈ x, p ^ n.factorization p) * ∏ p ∈ (n.primeFactors \ x), p ^ n.factorization p := by rw [mul_comm, Finset.prod_sdiff hx]
      have hanti : n / (∏ p ∈ x, p ^ n.factorization p) = ∏ p ∈ (n.primeFactors \ x), p ^ n.factorization p := by
        nth_rw 1 [hn]
        rw [Nat.mul_div_cancel_left]
        apply Finset.prod_pos
        intro i hi
        apply Nat.pos_pow_of_pos
        exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors (hx hi))
      have hpcop : (∏ p ∈ x, p ^ n.factorization p).Coprime (n / ∏ p ∈ x, p ^ n.factorization p) := by
        rw [hanti, Nat.coprime_prod_left_iff]
        intro p1 hp1
        rw [Nat.coprime_prod_right_iff]
        intro p2 hp2
        have ⟨hp2_1, hp2_2⟩ := Finset.mem_sdiff.mp hp2
        apply Nat.coprime_pow_primes
        . exact Nat.prime_of_mem_primeFactors (hx hp1)
        · exact Nat.prime_of_mem_primeFactors hp2_1
        exact Membership.mem.ne_of_not_mem hp1 hp2_2
      constructor
      · constructor
        · nth_rw 2 [hn]
          apply dvd_mul_right
        · positivity
      · exact hpcop
    exact ⟨hMapsTo, hInjOn, hSurjOn⟩
  have (n : ℕ) (hnone : 1 < n) : (Sb' n).card = (n.primeFactors.powerset).card := by
    calc
      (Sb' n).card = (Sb' n : Set ℕ).toFinset.card := by simp
      _ = (Sb' n : Set ℕ).ncard := by rw [Set.ncard_eq_toFinset_card']
      _ = ((g n) '' (n.primeFactors.powerset: Set (Finset ℕ))).ncard := by rw [Set.BijOn.image_eq (hpFBijSb' n hnone)]
      _ = (n.primeFactors.powerset: Set (Finset ℕ)).ncard := by rw [Set.ncard_image_of_injOn (Set.BijOn.injOn (hpFBijSb' n hnone))]
      _ = (n.primeFactors.powerset: Set (Finset ℕ)).toFinset.card := by rw [Set.ncard_eq_toFinset_card']
      _ = (n.primeFactors.powerset).card := by simp
  rw [this _ (by rw [Nat.one_lt_factorial]; norm_num)]
  -- In particular, There are 8 [prime numbers](https://artofproblemsolving.com/wiki/index.php/Prime_number) less than 20 ($2, 3, 5, 7, 11, 13, 17, 19$), and each can only be a factor of one of $a$ or $b$.
  have hfactorialPrimeFactors (n : ℕ) : n.factorial.primeFactors = { n ∈ Finset.Icc 2 n | Nat.Prime n } := by
    ext p
    simp
    constructor
    · intro ⟨hpprime, hpdvdnf, _hnpos⟩
      exact ⟨⟨Nat.Prime.two_le hpprime, (Nat.Prime.dvd_factorial hpprime).mp hpdvdnf⟩, hpprime⟩
    · intro ⟨⟨_h2le, hpdvdnf⟩, hpprime⟩
      have hpdvdhf : p ∣ n.factorial := (Nat.Prime.dvd_factorial hpprime).mpr hpdvdnf
      exact ⟨hpprime, hpdvdhf, pos_iff_ne_zero.mp (Nat.factorial_pos n)⟩
  -- There are 8 [prime numbers](https://artofproblemsolving.com/wiki/index.php/Prime_number) less than 20 ($2, 3, 5, 7, 11, 13, 17, 19$)
  rw [hfactorialPrimeFactors 20]
  have hp20 : { n ∈ Finset.Icc 2 20 | Nat.Prime n } = {2, 3, 5, 7, 11, 13, 17, 19} := by
    ext p
    simp
    constructor
    · intro ⟨⟨hlb, hub⟩, hprime⟩
      interval_cases p <;> norm_num at hprime <;> tauto
    · intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num
  rw [hp20, Finset.card_powerset]
  simp
