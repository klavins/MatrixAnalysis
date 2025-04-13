import Mathlib

theorem matrix_eq_all
  {n m:ℕ} {A : Matrix (Fin n) (Fin m) ℂ} {B : Matrix (Fin n) (Fin m) ℂ}
  : A = B ↔ ∀ i j, A i j = B i j := by
  constructor
  . intro h i j
    exact congrFun (congrFun h i) j
  . exact Matrix.ext

theorem matrix_neq_exists
  {n m:ℕ} {A : Matrix (Fin n) (Fin m) ℂ} {B : Matrix (Fin n) (Fin m) ℂ}
  : A ≠ B ↔ ∃ i j, A i j ≠ B i j := by
  simp[matrix_eq_all]
