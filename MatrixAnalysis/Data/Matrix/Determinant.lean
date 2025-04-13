import Mathlib

def row_minor
    {n m: ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (k: (Fin m))
    : Matrix (Fin (m-1)) (Fin n) ℚ :=
    Matrix.of λ i j =>
      if (Fin.mk i (Nat.lt_of_lt_pred i.isLt)) < k
      then A (Fin.mk i (Nat.lt_of_lt_pred i.isLt)) j
      else A (Fin.mk (i+1) (Nat.add_lt_of_lt_sub i.isLt)) j

def col_minor
    {n m: ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (k: (Fin n))
    : Matrix (Fin m) (Fin (n-1)) ℚ :=
    Matrix.of λ i j =>
      if (Fin.mk j (Nat.lt_of_lt_pred j.isLt)) < k
      then A i (Fin.mk j (Nat.lt_of_lt_pred j.isLt))
      else A i (Fin.mk (j+1) (Nat.add_lt_of_lt_sub j.isLt))

def row_col_minor
    {n m: ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : (Fin m)) (j : (Fin n))
    : Matrix (Fin (m-1)) (Fin (n-1)) ℚ :=
    row_minor (col_minor A j) i

def A : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,2;0,3,0;4,0,5]

#eval row_minor A 1
#eval row_minor A 2
#eval row_col_minor A 1 1

def q : (Fin 5) := 3

variable (e : (Fin 4) ≃ (Fin 4))
#check e 1

#eval (-1)^3

def s {n:ℕ} (k : Fin n) := if Odd k.val then -1 else 1

def det {n:ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :=
  match n with
  | Nat.zero => 1
  | Nat.succ _ => ∑ j, (s j) • ((A 0 j) * det (row_col_minor A 0 j))

#eval det A
#eval A.det

/- This version of the theorem basically just wraps around Mathlib's -/
theorem det_mult'
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℚ)
  : Matrix.det (A*B) = (Matrix.det A) * (Matrix.det B) := by
  exact Matrix.det_mul A B

theorem det_mult
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℚ)
  : det (A*B) = (det A) * (det B) := by
  sorry
