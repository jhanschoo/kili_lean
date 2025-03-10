import Mathlib

/- Let $S$ be the set of all rational numbers $r$, $0 < r < 1$, that have a repeating decimal expansion in the form $0.abcabcabc\ldots=0.\overline{abc}$, where the digits $a$, $b$, and $c$ are not necessarily distinct. To write the elements of $S$ as fractions in lowest terms, how many different numerators are required? -/
theorem AIME_96003 :
Set.ncard { n : ℤ | ∃ r : ℚ, 0 < r ∧ r < 1 ∧ r.num = n ∧
∃ a ∈ Finset.range 9, ∃ b ∈ Finset.range 9, ∃ c ∈ Finset.range 9, r = Rat.divInt (a * 100 + b * 10 + c) 999 } = 660 := by
  set S := { n ∈ Finset.Ioo (0 : ℤ) (999 : ℤ) | ∃ a ∈ Finset.range 9, ∃ b ∈ Finset.range 9, ∃ c ∈ Finset.range 9, (Rat.divInt (a * 100 + b * 10 + c) 999).num = n ∧ 0 < Rat.divInt (a * 100 + b * 10 + c) 999 ∧ Rat.divInt (a * 100 + b * 10 + c) 999 < 1 } with hS
  have : { n : ℤ | ∃ r : ℚ, 0 < r ∧ r < 1 ∧ r.num = n ∧
∃ a ∈ Finset.range 9, ∃ b ∈ Finset.range 9, ∃ c ∈ Finset.range 9, r = Rat.divInt (a * 100 + b * 10 + c) 999 } = S := by
    ext n
    simp [hS]
    intro x hxpos hxub hxnum a b c hx
    rw [← hxnum]
    constructor
    · positivity
    ·
