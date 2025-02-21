import Mathlib

set_option maxRecDepth 10000

/--
Every positive integer $k$ has a unique factorial base expansion $(f_1,f_2,f_3,\ldots,f_m)$, meaning that $k=1!\cdot f_1+2!\cdot f_2+3!\cdot f_3+\cdots+m!\cdot f_m$, where each $f_i$ is an integer, $0\le f_i\le i$, and $0 < f_m$. Given that $(f_1,f_2,f_3,\ldots,f_j)$ is the factorial base expansion of $16!-32!+48!-64!+\cdots+1968!-1984!+2000!$, find the value of $f_1-f_2+f_3-f_4+\cdots+(-1)^{j+1}f_j$.
-/
theorem number_theory_716 : ∃ (f : ℕ →₀ ℤ),
    (∀ (i:ℕ), f i ∈ Finset.Icc (0:ℤ) (i:ℤ)) ∧
    f.sum (fun i fi ↦ (fi:ℤ) * (i.factorial:ℤ)) =
    ((16).factorial :ℤ) + ∑ m ∈ Finset.Icc (1:ℕ) 62, (((32 * m + 16).factorial:ℤ) - ((32 * m).factorial :ℤ)) ∧
    f.sum (fun i fi ↦ (-1:ℤ) ^ (i + 1) * fi) = 495 := by
    -- Note that $1+\sum_{k=1}^{n-1} {k\cdot k!} = 1+\sum_{k=1}^{n-1} {((k+1)\cdot k!- k!)} = 1+\sum_{k=1}^{n-1} {((k+1)!- k!)} = 1 + ((2! - 1!) + (3! - 2!) + \cdots + (n! - (n-1)!)) = n!$.
  have factorial_sum (n : ℕ) : 1 + ∑ k ∈ Finset.range n, (k * k.factorial) = n.factorial := by
    calc
      1 + ∑ k ∈ Finset.range n, (k * k.factorial)
        = 1 + ∑ k in Finset.range n, ((k + 1) * k.factorial - k.factorial) := by
          congr; funext k
          rw [add_mul, one_mul, Nat.add_sub_self_right]
      _ = 1 + ∑ k in Finset.range n, ((k + 1).factorial - k.factorial) := by
          congr
      _ = 1 + (n.factorial - (0).factorial) := by
          rw [Finset.sum_range_tsub (Nat.monotone_factorial)]
      _ = n.factorial := Nat.add_sub_of_le (Nat.succ_le_of_lt (Nat.factorial_pos n))
  -- Thus for all $m\in\mathbb{N}$, $(32m+16)!-(32m)! = \left(1+\sum_{k=1}^{32m+15} {k\cdot k!}\right)-\left(1+\sum_{k=1}^{32m-1} {k\cdot k!}\right) = \sum_{k=32m}^{32m+15}k\cdot k!.$
  -- have factorial_sum_3216 (a b : ℕ) (m : ℕ) : ((32 * m + 16).factorial:ℤ) - ((32 * m).factorial:ℤ) = ∑ k ∈ Finset.Ico (32 * m) (32 * m + 16), (k:ℤ) * (k.factorial:ℤ)
  have factorial_sum' (a b : ℕ) (m : ℕ) : ((a * m + b).factorial:ℤ) - ((a * m).factorial:ℤ) = ∑ k ∈ Finset.Ico (a * m) (a * m + b), (k:ℤ) * (k.factorial:ℤ) := by
    calc
      ((a * m + b).factorial:ℤ) - ((a * m).factorial:ℤ)
        = (((1 + ∑ k ∈ Finset.range (a * m + b), k * k.factorial):ℕ):ℤ) - (((1 + ∑ k ∈ Finset.range (a * m), (k * k.factorial)):ℕ):ℤ) := by
          rw [← factorial_sum, ← factorial_sum]
      _ = (((∑ k ∈ Finset.range (a * m + b), k * k.factorial):ℕ):ℤ) - (((∑ k ∈ Finset.range (a * m), k * k.factorial):ℕ):ℤ) := by norm_num
      _ = (∑ k ∈ Finset.range (a * m + b) \ Finset.range (a * m), (k * k.factorial):ℤ) := by
        push_cast
        rw [Finset.sum_sdiff_eq_sub (Finset.range_subset.mpr (by linarith : a * m ≤ a * m + b))]
      _ = ∑ k ∈ Finset.Ico (a * m) (a * m + b), (k:ℤ) * (k.factorial:ℤ) := by
        congr; ext x; simp ; constructor <;> intro <;> constructor <;> linarith
  -- So now, $-32!+48!-64!+\cdots+1968!-1984!+2000!&=16!+(48!-32!)+(80!-64!)\cdots+(2000!-1984!)=16! +\sum_{m=1}^{62}(32m+16)!-(32m)=16! +\sum_{m=1}^{62}\sum_{k=32m}^{32m+15}k\cdot k! $. Moreover, note that the ranges over which the inner sum is taken are pairwise disjoint for distinct $m$.
  set supp' := fun (u a b : ℕ) ↦ (Finset.Icc 1 u).biUnion (fun m ↦ Finset.Ico (a * m) (a * m + b)) with hsupp'
  have hpwdisj (u a b : ℕ) (hab : b < a) (hapos : 0 < a) : ((Finset.Icc 1 u) : Set ℕ).PairwiseDisjoint (fun m ↦ Finset.Ico (a * m) (a * m + b)) := by
    simp; intro m hm m' hm' hne; simp only [Set.mem_Icc, Function.onFun] at hm hm' ⊢
    have h_le (n n' : ℕ) (hlt : n < n') : Disjoint (Finset.Ico (a * n) (a * n + b)) (Finset.Ico (a * n') (a * n' + b)) := by
      rw [
        ←Set.toFinset_Ico (a * n) _,
        ← Set.toFinset_Ico (a * n') _,
        Set.disjoint_toFinset,
        Set.Ico_disjoint_Ico,
      ]
      calc
        min (a * n + b) (a * n' + b)
          ≤ (a * n + b) := by simp only [min_le_iff, le_refl, add_le_add_iff_right, true_or]
        _ ≤ (a * n + a) := by simp only [add_le_add_iff_left, Nat.le_of_lt hab]
        _ = (a * (n + 1)) := by simp [mul_add]
        _ ≤ (a * n') := by simp only [add_le_add_iff_right, mul_le_mul_left hapos, Nat.succ_le_of_lt hlt]
        _ ≤ max (a * n) (a * n') := by simp only [le_max_iff, le_refl, or_true]
    rcases Nat.lt_trichotomy m m' with (hm | rfl | hm)
    · exact h_le m m' hm
    · contradiction
    · exact (h_le m' m hm).symm
  have factorial_sum_sum (u a b : ℕ) (hab : b < a) (hapos : 0 < a) : ∑ m ∈ Finset.Icc 1 u, (((a * m + b).factorial:ℤ) - ((a * m).factorial :ℤ)) = ∑ k ∈ supp' u a b, (k:ℤ) * (k.factorial:ℤ)
  := by
    calc
      ∑ m ∈ Finset.Icc 1 u, (((a * m + b).factorial:ℤ) - ((a * m).factorial :ℤ))
        = ∑ m ∈ Finset.Icc 1 u, ∑ k ∈ Finset.Ico (a * m) (a * m + b), (k:ℤ) * (k.factorial:ℤ) := by simp_rw [factorial_sum']
      _ = ∑ k ∈ supp' u a b, (k:ℤ) * (k.factorial:ℤ) := by
        rw [Finset.sum_biUnion (hpwdisj u a b hab hapos)]
  -- Therefore put $f_{16} = 1$, and $f_k=k$ whenever $32m\le k \le 32m+15$ for any $m=1,2,\ldots,62$, and $f_k = 0$ for all other $k$. We verify that this $f$ satisfies being the desired factorial base expansion.
  set f' := fun (u a b i : ℕ) ↦ if i ∈ supp' u a b then (i:ℤ) else (0:ℤ) with hf'
  have f'_nonsupp (u a b i : ℕ) : i ∉ supp' u a b → f' u a b i = 0 := by
    intro contra
    simp only [hf', contra, ↓reduceIte, not_true_eq_false, ne_eq, not_false_eq_true]
  set f := fun (u a b : ℕ) ↦ (fun₀ | b => (1:ℤ)) + Finsupp.onFinset (supp' u a b) (f' u a b) (by intro i; contrapose; simp only [ne_eq, Decidable.not_not]; exact (f'_nonsupp u a b i)) with hf
  have supp_bounds (x u a b : ℕ) (hx : x ∈ supp' u a b) : a ≤ x ∧ x < a * u + b := by
    simp [hsupp'] at hx
    rcases hx with ⟨m, ⟨hml, hmu⟩, ⟨hl, hu⟩⟩
    constructor
    · calc
        a = a * 1 := by simp
        _ ≤ a * m := by rel [hml]
        _ ≤ x := hl
    · calc
        x < a * m + b := hu
        _ ≤ a * u + b := by rel [hmu]
  have hbninsupp' (u a b : ℕ) (hab : b < a) : ¬b ∈ supp' u a b := by
    intro contra
    specialize supp_bounds b u a b contra
    linarith
  use f 62 32 16
  constructor
  · -- we first verify that the $f_i$ satisfy $0\le f_i\le i$.
    intro i; simp [f]
    by_cases h16 : i = 16
    · simp only [h16, Finsupp.single_eq_same, hbninsupp' 62 32 16 (by norm_num),
      not_false_eq_true, f'_nonsupp 62 32 16 16, add_zero, zero_le_one, Nat.cast_ofNat,
      Nat.one_le_ofNat, and_self]
    have h16supp : (fun₀ | 16 => (1:ℤ)) i = 0 := by
      rw [eq_comm] at h16
      rw [Finsupp.single_eq_of_ne h16]
    simp [h16supp]
    by_cases h' : i ∈ supp' 62 32 16
      <;> simp only [h', ↓reduceIte, Nat.cast_nonneg, le_refl, and_self, f']
  constructor
  · -- we now verify that the factorial sum is as desired.
    rw [
      factorial_sum_sum 62 32 16 (by norm_num) (by norm_num),
      hf,
      Finsupp.sum_add_index (by simp) (by intro x _ b1 b2; rw [add_mul]),
      Finsupp.sum_single_index (by simp),
      one_mul,
      Finsupp.onFinset_sum (by intro a; contrapose; simp only [ne_eq, Decidable.not_not]; exact (f'_nonsupp 62 32 16 a)) (by simp),
      hf',
    ]
    dsimp
    conv_lhs => rhs; rhs; ext x; rw [ite_mul, zero_mul]
    rw [
      Finset.sum_ite_mem,
      Finset.inter_self
    ]
  · -- finally, we compute the desired sum.
    rw [
      hf,
      Finsupp.sum_add_index (by simp) (by intro x _ b1 b2; rw [mul_add]),
      Finsupp.sum_single_index (by simp),
      mul_one,
      Finsupp.onFinset_sum (by intro a; contrapose; simp only [ne_eq, Decidable.not_not]; exact (f'_nonsupp 62 32 16 a)) (by simp),
      hf',
    ]
    dsimp
    conv_lhs => rhs; rhs; ext x; rw [mul_ite, mul_zero]
    rw [
      Finset.sum_ite_mem (supp' 62 32 16) (supp' 62 32 16) (fun x : ℕ ↦ (-1:ℤ) ^ (x + 1) * (x:ℤ)),
      Finset.inter_self,
      hsupp',
      Finset.sum_biUnion (hpwdisj 62 32 16 (by norm_num) (by positivity)),
    ]
    -- at this point it remains to show that -1 + ∑ x ∈ Finset.Icc 1 62, ∑ i ∈ Finset.Ico (32 * x) (32 * x + 16), (-1) ^ (i + 1) * ↑i = 495
    -- we first show that the inner sum is 8 for all x
    have (x : ℕ) :=
      calc
        ∑ i ∈ Finset.Ico (32 * x) (32 * x + 16), (-1: ℤ) ^ (i + 1) * (i:ℤ)
          = (∑ i ∈ {i ∈ (Finset.Ico (32 * x) (32 * x + 16)) | i % 2 = 0}, (-1) ^ (i + 1) * (i:ℤ)) +
        ∑ i ∈ {i ∈ (Finset.Ico (32 * x) (32 * x + 16)) | i % 2 ≠ 0}, (-1) ^ (i + 1) * (i:ℤ) := by
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico (32 * x) (32 * x + 16)) (fun i : ℕ ↦ i % 2 = 0)]
        _ = (∑ i ∈ Finset.image (fun i ↦ (2 * i:ℕ)) (Finset.Ico (16 * x) (16 * x + 8)), -(i:ℤ)) +
        ∑ i ∈ Finset.image (fun i ↦ (2 * i + 1:ℕ)) (Finset.Ico (16 * x) (16 * x + 8)), (i:ℤ) := by rw [
          Finset.sum_congr
            (by
              apply Finset.ext; intro i; simp; constructor
              · intro ⟨⟨hlb, hub⟩, hieven⟩
                use i / 2; constructor
                · constructor
                  · rw [Nat.le_div_iff_mul_le (by norm_num)]; ring_nf at hlb ⊢; exact hlb
                  · rw [Nat.div_lt_iff_lt_mul (by norm_num)]; ring_nf at hub ⊢; exact hub
                · nth_rw 2 [← Nat.div_add_mod i 2]; rw [hieven]; simp
              · intro ⟨a, ⟨⟨hlb, hub⟩, hieven⟩⟩
                subst hieven
                apply Nat.mul_le_mul_left 2 at hlb; rw [← mul_assoc] at hlb; simp at hlb
                apply (fun x ↦ Nat.mul_lt_mul_of_pos_left x (by norm_num : 0 < 2)) at hub; rw [mul_add, ← mul_assoc] at hub; simp at hub ⊢; tauto
            : {i ∈ (Finset.Ico (32 * x) (32 * x + 16)) | i % 2 = 0} = Finset.image (fun i ↦ (2 * i:ℕ)) (Finset.Ico (16 * x) (16 * x + 8)))
            (by
              intro i hi; simp at hi
              rcases hi with ⟨a, ⟨_, hieven⟩⟩
              rw [← hieven, pow_succ]; simp
            : ∀ i ∈ Finset.image (fun i ↦ (2 * i:ℕ)) (Finset.Ico (16 * x) (16 * x + 8)), (-1:ℤ) ^ (i + 1) * (i:ℤ) = -(i:ℤ)),
          Finset.sum_congr (by
              apply Finset.ext; intro i; simp; constructor
              · intro ⟨⟨hlb, hub⟩, hiodd⟩
                use i / 2; constructor
                · constructor
                  · rw [Nat.le_div_iff_mul_le (by norm_num)]; ring_nf at hlb ⊢; exact hlb
                  · rw [Nat.div_lt_iff_lt_mul (by norm_num)]; ring_nf at hub ⊢; exact hub
                · nth_rw 2 [← Nat.div_add_mod i 2]; rw [hiodd]
              · intro ⟨a, ⟨⟨hlb, hub⟩, hiodd⟩⟩
                subst hiodd
                apply Nat.mul_le_mul_left 2 at hlb; rw [← mul_assoc] at hlb; simp at hlb; apply Nat.le_succ_of_le at hlb
                apply Nat.le_of_lt_succ at hub
                have :=
                  calc
                    2 * a + 1 ≤ 2 * (16 * x + 7) + 1 := by rel [hub]
                    _ = 32 * x + 15 := by ring
                    _ < 32 * x + 15 + 1 := by simp
                    _ = 32 * x + 16 := by ring
                rw [Nat.add_mod]
                simp [hlb, this]
            : {i ∈ (Finset.Ico (32 * x) (32 * x + 16)) | i % 2 ≠ 0} = Finset.image (fun i ↦ (2 * i + 1:ℕ)) (Finset.Ico (16 * x) (16 * x + 8)))
            (by
              intro i hi; simp at hi
              rcases hi with ⟨a, ⟨_, hiodd⟩⟩
              rw [← hiodd, pow_succ, pow_succ]; simp
            : ∀ i ∈ Finset.image (fun i ↦ (2 * i + 1:ℕ)) (Finset.Ico (16 * x) (16 * x + 8)), (-1:ℤ) ^ (i + 1) * (i:ℤ) = (i:ℤ)),
          ]
        _ = (∑ i ∈ Finset.Ico (16 * x) (16 * x + 8), -((2 * i:ℕ):ℤ)) +
        ∑ i ∈ Finset.Ico (16 * x) (16 * x + 8), ((2 * i + 1:ℕ):ℤ) := by rw [
          Finset.sum_image (by intro i _ i' _; intro h; exact Nat.mul_left_cancel (by norm_num) h),
          Finset.sum_image (by intro i _ i' _; intro h; exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h))]
        _ = ∑ i ∈ Finset.Ico (16 * x) (16 * x + 8), (-((2 * i:ℕ):ℤ) + (2 * i + 1:ℕ):ℤ) := by rw [← Finset.sum_add_distrib]
        _ = ∑ i ∈ Finset.Ico (16 * x) (16 * x + 8), 1 := by simp
        _ = 8 := by rw [Finset.sum_const]; simp
    conv_lhs => rhs; rhs; ext x; rw [this]
    -- and then we show that the outer sum is 62 * 8 = 496, giving -1 + 496 = 495
    rw [Finset.sum_const]; simp
