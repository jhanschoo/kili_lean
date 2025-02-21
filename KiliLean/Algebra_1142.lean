import Mathlib

/--
PROBLEM:
Members of the Rockham Soccer League buy socks and T-shirts. Socks cost $4 per pair and each T-shirt costs $5 more than a pair of socks. Each member needs one pair of socks and a shirt for home games and another pair of socks and a shirt for away games. If the total cost is $2366, how many members are in the League?
-/
theorem algebra_1142 (socks_cost tshirt_cost member_cost total_cost : ℚ) (num_members : ℕ) (hsocks_cost : socks_cost = 4) (htshirt_cost : tshirt_cost = socks_cost + 5) (hmember_cost : member_cost = socks_cost + tshirt_cost + socks_cost + tshirt_cost) (htotal_cost' : total_cost = 2366) (htotal_cost : total_cost = member_cost * num_members) : num_members = 91 := by
  -- Since T-shirts cost $5$ dollars more than a pair of socks, T-shirts cost $5+4=9$ dollars.
  have htshirt_cost' : tshirt_cost = 9 := by simp only [htshirt_cost, hsocks_cost]; norm_num
  -- Since each member needs $2$ pairs of socks and $2$ T-shirts, the total cost for $1$ member is $2(4+9)=26$ dollars.
  have hmember_cost' : member_cost = 26 := by simp only [hmember_cost, hsocks_cost, htshirt_cost']; norm_num
  -- Since $2366$ dollars was the cost for the club, and $26$ was the cost per member, the number of members in the League is $2366\div 26=\boxed{\mathrm{(B)}\ 91}$.
  have hnum_members : (num_members:ℚ) = 91 := by
    rw [htotal_cost', hmember_cost'] at htotal_cost
    calc
      (num_members:ℚ) = 26 * num_members / 26 := by ring
      _ = 2366 / 26 := by rw [htotal_cost]
      _ = 91 := by norm_num
  norm_cast at hnum_members
