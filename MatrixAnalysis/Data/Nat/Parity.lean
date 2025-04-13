import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.ModEq
import KlavLib.Data.Nat.Identities

/- # Useful Mathlib Theorems -/

#check Nat.not_even_iff_odd
#check Nat.not_odd_iff_even
#check odd_iff_exists_bit1
#check even_iff_exists_two_nsmul
#check even_iff_exists_two_mul
#check Even.add_self

#check Nat.ModEq.of_dvd
#check Nat.ModEq.of_mul_left


/- # Parity Definitions -/

def parity (x : ℕ) := x%2

def parity' (x : ℕ) := if Odd x then 1 else 0

theorem parity_alt {x : ℕ} : parity x = parity' x := by
  simp[parity,parity']
  by_cases ho : Odd x
  . simp[ho]
    exact Nat.odd_iff.mp ho
  . simp[ho]
    exact Nat.not_odd_iff.mp ho



/- # Odd and Even Theorems -/

theorem odd_eq_odd_iff_even_eq_even {x y:ℕ} : (Odd x ↔ Odd y) ↔ (Even x ↔ Even y) := by
  rw[←Nat.not_even_iff_odd,←Nat.not_even_iff_odd]
  exact Decidable.not_iff_not

theorem even_sum_evens {x y: ℕ} : Even (2*x+2*y) := by
  have : 2*x+2*y = 2*(x+y) := by linarith
  simp[this]

theorem not_odd_sum_evens {x y: ℕ} : ¬Odd (2*x+2*y) := by
  simp
  exact even_sum_evens

theorem odd_sum_evens_eq_false {x y: ℕ} : Odd (2*x+2*y) ↔ False := by
  simp
  exact even_sum_evens

theorem not_odd_sum_self {x:ℕ} : ¬Odd (x+x) := by simp

theorem odd_sum_self_eq_false {x:ℕ} : Odd (x+x) ↔ False := by simp

theorem odd_eq_rm_even_parts {x y: ℕ} : Odd (x + 2*y) ↔ Odd x := by

  by_cases ho : Odd x

  . obtain ⟨ j, hj ⟩ := odd_iff_exists_bit1.mp ho
    simp[hj]
    use j + y
    linarith

  . simp at ho
    obtain ⟨ j, hj ⟩ := even_iff_exists_two_mul.mp ho
    rw[hj]
    simp[odd_sum_self_eq_false,odd_sum_evens_eq_false]

theorem even_eq_rm_even_parts {x y: ℕ} : Even (x + 2*y) ↔ Even x := by
  rw[←Nat.not_odd_iff_even,←Nat.not_odd_iff_even]
  apply not_congr
  apply odd_eq_rm_even_parts

theorem even_even_to_odd_eq_odd {x y:ℕ} : Even x → Even y → (Odd x ↔ Odd y) := by
  rw[←Nat.not_even_iff_odd,←Nat.not_even_iff_odd]
  intro hx hy
  apply not_congr
  exact (iff_true_right hy).mpr hx




/- # Parity Related to Odd and Even -/

theorem parity_to_odd {x y: ℕ} : parity x = parity y ↔ (Odd x ↔ Odd y) := by

  constructor

  . intro h
    rw[parity_alt,parity_alt] at h
    simp[parity'] at h
    split_ifs at h
    . rename_i h1 h2
      simp_all
    . rename_i h1 h2
      simp_all
      exact even_even_to_odd_eq_odd h1 h2

  . intro h
    rw[parity_alt,parity_alt]
    unfold parity'
    by_cases ho : Odd x
    repeat
    . simp[ho]
      rw[h] at ho
      simp[ho]

theorem parity_to_even (x y: ℕ) : parity x = parity y ↔ (Even x ↔ Even y) := by
  rw[←Nat.not_odd_iff_even, ←Nat.not_odd_iff_even]
  rw[parity_to_odd]
  exact Iff.symm Decidable.not_iff_not

theorem parity_to_odd_even (x y: ℕ) : parity x = parity y ↔ (Even x ∧ Even y) ∨ (Odd x ∧ Odd y) := by
  rw[parity_to_even]
  rw[←Nat.not_even_iff_odd, ←Nat.not_even_iff_odd]
  exact Decidable.iff_iff_and_or_not_and_not





/- # Modular Arithmetic -/

theorem mod_factor_2 {x y a b: ℕ} : a = 2*b → x ≡ y [MOD a] → x ≡ y [MOD b] := by
  intro h1 h2
  rw[h1] at h2
  exact Nat.ModEq.of_mul_left 2 h2

theorem mod_to_exists {x y m : ℕ} (gxy : x > y): x ≡ y [MOD m] ↔ ∃ k, x = y + m*k := by

  have gexy : x ≥ y := by exact Nat.le_of_succ_le gxy
  constructor

  . intro hxy
    rw[Nat.ModEq.comm,Nat.modEq_iff_dvd'] at hxy
    . simp[Nat.instDvd] at hxy
      obtain ⟨ c, hc ⟩ := hxy
      apply add_both_sides y at hc
      have : x - y + y = x := by exact Nat.sub_add_cancel gexy
      rw[this] at hc
      use c
      rw[add_comm] at hc
      exact hc
    . convert gexy

  . intro h
    obtain ⟨ c, hc ⟩ := h
    simp[hc,Nat.ModEq]

theorem eq_mod_to_exists {x y m : ℕ} (gxy : x = y): x ≡ y [MOD m] ↔ ∃ k, x = y + m*k := by
  constructor
  . intro h
    use 0
    rw[gxy]
    linarith
  . intro h
    simp[gxy]
    rfl

theorem mod_pow_le {x y n m: ℕ} (hn : m ≤ n)
  : x ≡ y [MOD 2^n] → x ≡ y [MOD 2^m] := by
  intro h
  have : ∃ k, k*(2^m) = 2^n := by
    use 2^(n-m)
    exact Nat.pow_sub_mul_pow 2 hn
  obtain ⟨ k, hk ⟩ := this
  rw[←hk] at h
  exact Nat.ModEq.of_mul_left k h



/- # Relating Mod2 to Odd/Even-/

theorem mod_2_to_odd_eq {x y : ℕ} : x ≡ y [MOD 2] → (Odd x ↔ Odd y) := by
  intro h
  by_cases hxy : x > y
  . obtain ⟨ h, hk ⟩ := (mod_to_exists hxy).mp h
    rw[hk,odd_eq_rm_even_parts]
  by_cases hyx : y > x
  . apply Nat.ModEq.symm at h
    obtain ⟨ h, hk ⟩ := (mod_to_exists hyx).mp h
    rw[hk,odd_eq_rm_even_parts]
  . have : x = y := by linarith
    rw[this]

theorem mod_2n_to_odd_eq {x y n: ℕ} (hn : n > 0) : x ≡ y [MOD 2^n] → (Odd x ↔ Odd y) := by
  intro h
  have : 2^n = (2^(n-1))*2 := Eq.symm (Nat.two_pow_pred_mul_two hn)
  rw[this] at h
  have := Nat.ModEq.of_mul_left (2^(n-1)) h
  exact mod_2_to_odd_eq this

theorem mod_div_2 {x y n : ℕ} : Even x → Even y → x ≡ y [MOD 2^(n+1)] → x/2 ≡ y/2 [MOD 2^n] := by
  intro ⟨ k, hk ⟩ ⟨ j, hj ⟩ h
  have : 2^(n+1) = 2 * 2^n := by exact Nat.pow_succ'
  rw[this] at h
  have : j+j = 2*j := by exact Eq.symm (Nat.two_mul j)
  simp_all[this]
  have : k+k = 2*k := by exact Eq.symm (Nat.two_mul k)
  simp_all[this]
  exact (Nat.ModEq.mul_left_cancel_iff' (by simp)).mp h

theorem mod_div_2_alt {x y n : ℕ} (hn: n>0) : 2*x ≡ 2*y [MOD 2^n] → x ≡ y [MOD 2^(n-1)] := by
  intro h
  have : n = (n-1) + 1 := by exact (Nat.sub_eq_iff_eq_add hn).mp rfl
  rw[this] at h
  have := @mod_div_2 (2*x) (2*y) (n-1) (even_two_mul x) (even_two_mul y) h
  simp at this
  exact this

theorem even_to_mod2 {x : ℕ} : Even x ↔ x ≡ 0 [MOD 2] := by
  constructor
  . intro ⟨ j, hj ⟩
    simp[hj]
    refine Nat.modEq_zero_iff_dvd.mpr ?_
    exact Nat.dvd_mul_right 2 j
  . intro h
    exact Nat.even_iff.mpr h

theorem odd_to_mod2 {x : ℕ} : Odd x ↔ x ≡ 1 [MOD 2] := by
  constructor
  . intro ⟨ j, hj ⟩
    simp[hj]
    have h1 : 2*j ≡ 0 [MOD 2] := by refine even_to_mod2.mp ?_; exact even_two_mul j
    have h2 : 1 ≡ 1 [MOD 2] := by exact rfl
    refine Nat.ModEq.add h1 h2

  . intro h
    exact Nat.odd_iff.mpr h


/- # Relating Mod2 to Parity -/

theorem mod_2n_to_parity {x y n: ℕ} (hn : n > 0) : x ≡ y [MOD 2^n] → parity x = parity y := by
  intro h
  exact parity_to_odd.mpr (mod_2n_to_odd_eq hn h)

theorem mod_2_to_parity {x y : ℕ} : x ≡ y [MOD 2] → parity x = parity y := by
  intro h
  have : 2 = 2^1 := rfl
  rw[this] at h
  refine mod_2n_to_parity ?_ h
  decide

theorem parity_to_mod2 {x y: ℕ} : parity x = parity y ↔ x ≡ y [MOD 2] := by

  constructor

  . rw[parity_to_odd_even]
    intro h
    apply Or.elim h
    . intro ⟨ hx, hy ⟩
      simp_all[even_to_mod2]
      exact Nat.ModEq.trans hx (id (Nat.ModEq.symm hy))

    . intro ⟨ hx, hy⟩
      simp_all[odd_to_mod2]
      exact Nat.ModEq.trans hx (id (Nat.ModEq.symm hy))

  . intro h
    exact mod_2_to_parity h
