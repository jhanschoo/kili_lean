import Mathlib

/- There are $n$ mathematicians seated around a circular table with $n$ seats numbered $1,$ $2,$ $3,$ $...,$ $n$ in clockwise order. After a break they again sit around the table. The mathematicians note that there is a positive integer $a$ such that


($1$) for each $k,$ the mathematician who was seated in seat $k$ before the break is seated in seat $ka$ after the break (where seat $i + n$ is seat $i$);


($2$) for every pair of mathematicians, the number of mathematicians sitting between them after the break, counting in both the clockwise and the counterclockwise directions, is different from either of the number of mathematicians sitting between them before the break.

Find the number of possible values of $n$ with $1 < n < 1000.$ -/
theorem number_theory_95127 :
    Set.ncard {n : ℕ | 1 < n ∧ n < 1000 ∧ ∃ a : ℕ, 0 < a ∧
      (∀ k : Fin n, (k * a) % n = k) ∧
      (∀ i j : Fin n, i ≠ j → (Nat.card {x | x ∈ Finset.Ioo i j}) ≠
        (Nat.card {x | x ∈ Finset.Ioo j i}))} = 332 := by sorry
