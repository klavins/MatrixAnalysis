import Mathlib

namespace MatrixAnalysis

def is_eigenvalue {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :=
  ∃ v : Matrix (Fin n) (Fin 1) ℂ, v ≠ 0 ∧ A*v = s•v

def is_eigen_pair
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v : Matrix (Fin n) (Fin 1) ℂ) :=
  v ≠ 0 ∧ A*v = s•v

def spectrum {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) := { s : ℂ | is_eigenvalue A s}

/- The next two theorems are straightforward helpers for certain proof situations. -/

@[simp]
theorem is_eigenvector_for_simp
  {n:ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {s : ℂ} {v : Matrix (Fin n) (Fin 1) ℂ}
  : is_eigen_pair A s v ↔ v ≠ 0 ∧ A*v = s•v := by
    rw[is_eigen_pair]

#print  is_eigenvector_for_simp

theorem eigen_value_from_pair
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v : Matrix (Fin n) (Fin 1) ℂ)
  : is_eigen_pair A s v → is_eigenvalue A s := by
    intro h
    use v
    simp_all

end MatrixAnalysis
