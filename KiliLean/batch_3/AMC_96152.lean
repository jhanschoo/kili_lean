import Mathlib

/- A particular $12$-hour digital clock displays the hour and minute of a day. Unfortunately, whenever it is supposed to display a $1$, it mistakenly displays a $9$. For example, when it is 1:16 PM the clock incorrectly shows 9:96 PM. What fraction of the day will the clock show the correct time?

$\mathrm{(A)}\ \frac 12\qquad \mathrm{(B)}\ \frac 58\qquad \mathrm{(C)}\ \frac 34\qquad \mathrm{(D)}\ \frac 56\qquad \mathrm{(E)}\ \frac {9}{10}$ -/
theorem number_theory_93636
    (T W : Finset (ℕ × ℕ))
    (hT : T = Finset.Icc 1 12 ×ˢ Finset.Icc 0 59)
    (hW : W = { t ∈ T | t.1 % 10 = 1 ∨ t.1 / 10 = 1 ∨ t.2 % 10 = 1 ∨ t.2 / 10 = 1 }) :
    ((T \ W).card : ℚ) / T.card = 1 / 2 := by
  -- We directly observe that the entire hours 1, 10, 11, 12 will be displayed incorrectly
  set ph := (fun (h : ℕ) ↦ h ∈ ({1, 10, 11, 12} : Finset ℕ)) with hph
  set Wh := { h ∈ Finset.Icc 1 12 | ph h } with hWh
  have Whcard : Wh.card = 4 := by congr
  -- We also directly observe that the clock is wrong when the minutes are the following:
  set pm := (fun (m : ℕ) ↦ m ∈ ({10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 21, 31, 41, 51} : Finset ℕ)) with hpm
  set Wm := { m ∈ Finset.Icc 0 59 | pm m } with hWm
  have Wmcard : Wm.card = 15 := by congr
  -- We prove that these are exactly the wrong times:
  have hWhm : W = Wh ×ˢ Finset.Icc 0 59 ∪ Finset.Icc 1 12 ×ˢ Wm := by
    refine le_antisymm ?_ ?_
    · intro x hx
      simp [hW] at hx
      simp [hWh, hWm, -Finset.mem_Icc]
      rcases hx with ⟨hxT, hh1 | hh2 | hm1 | hm2⟩
        <;> [left;left;right;right]
        <;> rw [hT, Finset.mem_product] at hxT
        <;> [refine ⟨⟨hxT.1, ?_⟩, hxT.2⟩; refine ⟨⟨hxT.1, ?_⟩, hxT.2⟩; refine ⟨hxT.1, ⟨hxT.2, ?_⟩⟩; refine ⟨hxT.1, ⟨hxT.2, ?_⟩⟩]
        <;> simp [hph, hpm]
        <;> simp at hxT
        <;> omega
    · intro x hx
      simp [hWh, hWm] at hx
      simp [hW, hT]
      rcases hx with hxh | hxm
      · refine ⟨⟨hxh.1.1, hxh.2⟩, ?_⟩
        simp [hph] at hxh
        omega
      · refine ⟨⟨hxm.1, hxm.2.1⟩, ?_⟩
        simp [hpm] at hxm
        omega
  -- So the number of wrong times W.card can be obtained from counting the
  -- number of wrong times due to hour, and for each hour that is correct
  -- the number of wrong times due to minutes
  have hWcard : W.card = 360 := by
    rw [hWhm, Finset.card_union, Finset.product_inter_product, Finset.card_product]
    rw [(by simp [hWh] : Wh ∩ Finset.Icc 1 12 = Wh)]
    rw [(by simp [hWm] : Finset.Icc 0 59 ∩ Wm = Wm)]
    simp [Whcard, Wmcard]
  have hTcard : T.card = 720 := by simp [hT]
  rw [Finset.card_sdiff]
  · simp [hWcard, hTcard]; ring
  · rw [hWhm, hWh, hWm, hT, Finset.union_subset_iff]
    refine ⟨Finset.product_subset_product_left ?_, Finset.product_subset_product_right ?_⟩ <;> simp
