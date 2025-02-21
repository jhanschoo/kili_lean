import Mathlib

/--
PROBLEM:
Let $S$ be a list of positive integers--not necessarily distinct--in which the number $68$ appears. The average (arithmetic mean) of the numbers in $S$ is $56$. However, if $68$ is removed, the average of the remaining numbers drops to $55$. What is the largest number that can appear in $S$?
-/

theorem algebra_694'
  -- Let $P$ be a property on a list of integers
  (P : Multiset ℤ → Prop)
  -- Such that if $S$ satisfies $P$,
  (hP : ∀ (S : Multiset ℤ), P S = (
    -- it is a list of positive integers
    (∀ x ∈ S, 0 < x) ∧
    ∃ (T : Multiset ℤ),
      -- in which the number $68$ appears at least one time
      S = 68 ::ₘ T ∧
      -- and the average of the numbers in $S$ is $56$,
      S.sum = 56 * (Multiset.card S : ℤ) ∧
      -- and the average of the remaining numbers is $55$,
      T.sum = 55 * (Multiset.card T : ℤ)))
  -- Then 649 can appear in a list $S$ that satisfies $P$
  : (∃ S, P S ∧ 649 ∈ S) ∧
  -- and it is the largest number that can appear in any such $S$
  (∀ S, P S → ∀ x ∈ S, x ≤ 649) := by
  constructor
  -- We first show that $649$ can appear in a list $S$ that satisfies $P$.
  -- Namely, have $S$ be the list of $13$ elements containing $68$, $649$, and $11$ copies of 1.
  · set Trest := Multiset.replicate 11 (1 : ℤ) with hTrest
    set T := 649 ::ₘ Trest with hT
    set S := 68 ::ₘ T with hS
    use S
    constructor
    · rw [hP]
      constructor
      · -- Indeed, all its elements are positive.
        simp [hS, hT, hTrest]
      use T
      constructor
      · exact hS
      -- Next, the sum of the elements in $S$ is $56 \times 13 = 728$,
      -- so the average of the elements in $S$ is $56$.
      -- Moreover, the sum of the elements in $S$ with $68$ removed is $55 \times 12 + 660$, so the average of its elements is $55$.
      constructor <;> simp [hS, hT, hTrest]
    · -- Finally, indeed, 649 is in $S$.
      simp [hS, hT]
    -- We now show that $649$ is the largest number that can appear in any such $S$. Consider an $x$ in any $S$ that satisfies $P$.
  · intro S hPS x hxS
    rw [hP] at hPS
    rcases hPS with ⟨hpos, T, ⟨hs68, hsavg, htavg⟩⟩
    -- First express the means in terms of totals of the numbers in the list instead. The total of the numbers in $S$ is $56$ times the number of elements in $S$, and the total of the numbers in the list with $68$ removed is that less $68$.
    have hsavg' : 68 + T.sum = 56 * (Multiset.card T + 1) := by
      calc
        68 + T.sum = (68 ::ₘ T).sum := by rw [Multiset.sum_cons]
        _ = S.sum := by rw [hs68]
        _ = 56 * Multiset.card S := by rw [hsavg]
        _ = 56 * (Multiset.card T + 1) := by congr; rw [hs68, Multiset.card_cons]
    --  But the total of the numbers in the list with $68$ removed is also $55$ times one less the size of $S$. We substitute this into the previous equation,
    rw [htavg] at hsavg'
    -- and discover that the size $S$ is $13$.
    have hTcard : Multiset.card T = 12 := by linarith
    rw [hs68, Multiset.mem_cons] at hxS
    cases hxS
    · case intro.intro.inl h => linarith
    · case intro.intro.inr hx =>
      -- Now, aiming to derive a contradiction, suppose that $x > 649$.
      by_cases hxgt649 : x > 649
      -- We proceed to show that this causes the total of the numbers in $S$ to exceed $600$.
      · have hsum : 660 < Multiset.sum T := by
          rw [← Multiset.sum_filter_add_sum_filter_not (fun a => a = x)]
          have hplus := Multiset.filter_add_not (fun a => a = x) T
          have hxrep : x ∈ Multiset.filter (fun a => a = x) T := Multiset.mem_filter_of_mem hx rfl
          set Tneq := T.filter (fun a => ¬a = x) with hTneq
          rw [Multiset.filter_eq'] at *
          have Tpnempty : ∃ (k : ℕ), k + 1 = Multiset.count x T := by
            rcases Multiset.mem_replicate.mp hxrep with ⟨hnempty, _⟩
            set n := Multiset.count x T
            use n - 1
            exact Nat.succ_pred_eq_of_ne_zero hnempty
          rcases Tpnempty with ⟨k, Tpnempty⟩
          rw [← Tpnempty, Multiset.replicate_succ, Multiset.sum_cons, add_assoc, ← Multiset.sum_add]
          rw [← Tpnempty, Multiset.replicate_succ, Multiset.cons_add] at hplus
          set Trest := Multiset.replicate k x + Tneq with hTrest
          -- In particlear, we just have to show that the remaining numbers in $S$ other than $68$ and $x$ total to at least $11$.
          have : 11 ≤ Trest.sum := by
            rw [← hplus] at hTcard
            simp at hTcard
            calc
              (11 : ℤ) = Multiset.card Trest := by rw [hTcard]; simp
              _ = (Multiset.replicate (Multiset.card Trest) 1).sum := by rw [Multiset.sum_replicate]; simp
              _ = (Multiset.map (Function.const ℤ 1) Trest).sum := by rw [Multiset.map_const]
              _ ≤ Trest.sum := by
                apply Multiset.sum_map_le_sum
                · simp
                  intro x' hx'
                  have : x' ∈ S := by
                    rw [hs68, ← hplus]
                    apply Multiset.mem_cons_of_mem
                    apply Multiset.mem_cons_of_mem
                    exact hx'
                  apply hpos x' this
          linarith
        linarith
      · linarith
