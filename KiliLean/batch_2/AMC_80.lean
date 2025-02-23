import Mathlib

/- Steve wrote the digits $1$, $2$, $3$, $4$, and $5$ in order repeatedly from left to right, forming a list of $10,000$ digits, beginning $123451234512\ldots.$ He then erased every third digit from his list (that is, the $3$rd, $6$th, $9$th, $\ldots$ digits from the left), then erased every fourth digit from the resulting list (that is, the $4$th, $8$th, $12$th, $\ldots$ digits from the left in what remained), and then erased every fifth digit from what remained at that point. What is the sum of the three digits that were then in the positions $2019, 2020, 2021$?

$\textbf{(A)}\ 7 \qquad\textbf{(B)}\ 9 \qquad\textbf{(C)}\ 10 \qquad\textbf{(D)}\ 11 \qquad\textbf{(E)}\ 12$ -/
theorem AMC_80 (a bi b ci c di d : ℕ → ℕ)
    (ha : ∀ n, a n = match n with | n' + 5 => a n' | _ => n + 1)
    (hbi : ∀ n, bi n = match n with | n' + 2 => bi n' + 3 | _ => n)
    (hb : ∀ n, b n = a (bi n))
    (hci : ∀ n, ci n = match n with | n' + 3 => ci n' + 4 | _ => n)
    (hc : ∀ n, c n = b (ci n))
    (hdi : ∀ n, di n = match n with | n' + 4 => di n' + 5 | _ => n)
    (hd : ∀ n, d n = c (di n)) :
    d 2018 + d 2019 + d 2020 = 11 := by
  have ha' m j : a (j + 5 * m) = a j := by
    induction m with
    | zero => rw [Nat.mul_zero, Nat.add_zero]
    | succ m ih =>
        rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, ha]
        simp [ih]
  -- Given a sequence $a_0, a_1, a_2, \cdots$, and an positive integer $k>2$. If we erase every $k$th item in this sequence, and we name the result sequence $b_0, b_1, b_2, \cdots$, then $b_{(k-1)m+j}=a_{km+j}$ for each $m$ and $0 ≤ j < k$.
  -- For $k=3$, we have $b_{2m+j}=a_{3m+j}$.
  have hbi' m j (hj : j < 2) : bi (j + 2 * m) = j + 3 * m := by
    induction m with
    | zero =>
      rw [Nat.mul_zero, Nat.add_zero, hbi]
      interval_cases j <;> dsimp
    | succ m ih =>
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, hbi]
      simp [ih, Nat.add_assoc]
  -- For $k=4$, we have $c_{3m+j}=b_{4m+j}$.
  have hci' m j (hj : j < 3) : ci (j + 3 * m) = j + 4 * m := by
    induction m with
    | zero =>
      rw [Nat.mul_zero, Nat.add_zero, hci]
      interval_cases j <;> dsimp
    | succ m ih =>
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, hci]
      simp [ih, Nat.add_assoc]
  -- For $k=5$, we have $d_{4m+j}=c_{5m+j}$.
  have hdi' m j (hj : j < 4) : di (j + 4 * m) = j + 5 * m := by
    induction m with
    | zero =>
      rw [Nat.mul_zero, Nat.add_zero, hdi]
      interval_cases j <;> dsimp
    | succ m ih =>
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, hdi]
      simp [ih, Nat.add_assoc]
  -- Therefore, $d_{2018}=d_{4·504+2}=c_{5·504+2}=c_{3·840+2}=b_{4·840+2}=b_{2·1681+0}=a_{3·1681+0}=a_{5·1008+3}=a_3=4$.
  rw [
    hd, (by norm_num : 2018 = 2 + 4 * 504), hdi' 504 2 (by norm_num),
    hc, (by norm_num : 2 + 5 * 504 = 2 + 3 * 840), hci' 840 2 (by norm_num),
    hb, (by norm_num : 2 + 4 * 840 = 0 + 2 * 1681), hbi' 1681 0 (by norm_num),
    (by norm_num : 0 + 3 * 1681 = 3 + 5 * 1008), ha', ha
  ]
  -- $d_{2019}=d_{4·504+3}=c_{5·504+3}=c_{3·841+0}=b_{4·841+0}=b_{2·1682+0}=a_{3·1682+0}=a_{5·1009+1}=a_1=2$.
  rw [
    hd, (by norm_num : 2019 = 3 + 4 * 504), hdi' 504 3 (by norm_num),
    hc, (by norm_num : 3 + 5 * 504 = 0 + 3 * 841), hci' 841 0 (by norm_num),
    hb, (by norm_num : 0 + 4 * 841 = 0 + 2 * 1682), hbi' 1682 0 (by norm_num),
    (by norm_num : 0 + 3 * 1682 = 1 + 5 * 1009), ha', ha
  ]
  -- $d_{2020}=d_{4·505+0}=c_{5·505+0}=c_{3·841+2}=b_{4·841+2}=b_{2·1683+0}=a_{3·1683+0}=a_{5·1009+4}=a_4=5$.
  rw [
    hd, (by norm_num : 2020 = 0 + 4 * 505), hdi' 505 0 (by norm_num),
    hc, (by norm_num : 0 + 5 * 505 = 2 + 3 * 841), hci' 841 2 (by norm_num),
    hb, (by norm_num : 2 + 4 * 841 = 0 + 2 * 1683), hbi' 1683 0 (by norm_num),
    (by norm_num : 0 + 3 * 1683 = 4 + 5 * 1009), ha', ha
  ]
  dsimp
