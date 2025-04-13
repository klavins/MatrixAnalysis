import Mathlib.Tactic

theorem add_both_sides {a b: ℕ} (c:ℕ): a = b → a + c = b + c := by
  intro h
  simp[h]

@[simp]
theorem two_mul_add_eq {x:ℕ} : x+x = 2*x := Eq.symm (Nat.two_mul x)



theorem pow_2n_fact_2 {n : ℕ} (hn : 0 < n) : 2^n = 2*(2^(n-1)) := by
  refine Eq.symm (mul_pow_sub_one ?_ 2)
  exact Nat.ne_zero_of_lt hn

theorem two_n_div_2 {x n : ℕ} (hn : 0 < n) : x * 2^n / 2 = x * 2^(n-1) := by

  calc x * 2^n / 2
  _  = x * (2*2^(n-1)) / 2 := by simp[pow_2n_fact_2 hn]
  _  = x * ((2^(n-1))*2) / 2 := by simp[mul_comm]
  _  = x * (2^(n-1)) * 2 / 2 := by ring_nf
  _  = x * (2^(n-1)) * (2 / 2)  := by simp
  _  = x * (2^(n-1)) * 1 := by rfl
  _  = x * (2^(n-1)) := by simp
  _  = _ := by simp
