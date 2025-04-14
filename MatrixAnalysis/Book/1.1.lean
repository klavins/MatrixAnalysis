import Mathlib
import MatrixAnalysis.Data.Polynomial.Basic
import MatrixAnalysis.Data.Matrix.Basic
import MatrixAnalysis.Data.Matrix.Eigenvalues
import MatrixAnalysis.Data.Matrix.Determinant

open MatrixAnalysis

/- # 1.1 The eigenvalue-eigenvector equation

We define a property to capture the definition of an eigenvalue of a square matrix. It asserts the existence of an non-zero vector that solves Av = λv. We use s instead of λ, since in Lean λ means something else.

One tricky thing to keep in mind is that in Lean A*v is matrix multiplication, whereas s•v is scalar multiplication of v by s. This will be a bit inconvenient, but we'll work around it (see the discussion below about polynomials). ∀

We also define a property to capture when s and v are eigenvalue, eigenvector pairs. And we define the spectrum of a matrix to be the set of all eigenvalues. All of these definitiions can be found in `MatrixAnalysis.Data.Matrix.Eigenvalues` -/

/- # Exercise (p35): Every non-zero scalar multiple of an eigenvector is an eigenvector.

Proving this amounts to unfolding the definitions, and then refolding with an arbitrary scalar multiple. -/

theorem eigenvector_scalar_multiple
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v : Matrix (Fin n) (Fin 1) ℂ)
  : is_eigen_pair A s v → ∀ (t : ℂ), t ≠ 0 → is_eigen_pair A s (t•v) := by
    intro h t tnz
    unfold is_eigen_pair
    unfold is_eigen_pair at h
    simp[h]
    exact ⟨ tnz, smul_comm t s v ⟩

/- # Example (p36): Verify the eigenvalues of a given matrix.

In the example below, we wish to start with a specific 2 × 2 matrix A and verify it has certain eigenvalue/eigenvector pairs. In the proofs, we need to show the eigenvalue equation holds, and show that the eigenvectors we choose are non-zero. The latter bit is harder than it should be. Two theorems we put in Data.Matrix.Basic can be used as helpers.
  - matrix_eq_all
  - matrix_neq_exists
These are both about the equality of two matrices. The first one says that two matrices are equal if they are equal at all locations. Now we can do the examples for a specific matrix. -/

namespace Example

  def A : Matrix (Fin 2) (Fin 2) ℂ := !![7,-2;4,1]

  example : is_eigen_pair A 3 !![1;2] := by
    unfold is_eigen_pair
    constructor
    . rw[matrix_neq_exists]
      use 0, 0
      simp
    . funext i j
      fin_cases i <;> fin_cases j <;> simp[A] <;> ring

  example : is_eigen_pair A 5 !![1;1] := by
    constructor
    . rw[matrix_neq_exists]
      use 0, 0
      simp
    . funext i j
      fin_cases i <;> fin_cases j <;> simp[A] <;> ring

end Example

/- # Polynomials acting on matrices

Given a polynomial p, there is a simple relationship between the eigenvalues of A and p(A): if s is an eigenvalue of A, then p(s) is an eigenvalue of p(A).

To get to this theorem, we have to either use Mathlib's polynomials or invent our own. Here, we take the latter approach, coming up with a very simple version of polynomials that hopefully work for most purposes in this book. We simply define a polynomial as function taking degrees i to coefficients pᵢ. The definition is in

  import MatrixAnalysis.Data.Polynomials.Basic

Then we define what it means to apply a polynomial to a given element. Note that in the code below, the element we apply a polynomial to can be from any ring. This allows us to use our polynomials with scalars and matrices, as required in this book. -/

/- Before we state the theorem, we first prove a helper theorem that describes the relationship between the eigenvalues of s of A and the eigenvalues sᵏ of Aᵏ. -/

theorem eig_eqn_pow
  {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {s : ℂ} {v :  Matrix (Fin n) (Fin 1) ℂ} (k:ℕ)
  : is_eigen_pair A s v → A^k * v = s^k • v := by
    intro h
    unfold is_eigen_pair at h
    induction k with
    | zero => simp
    | succ k ih =>
      have : A^(k+1) = A*A^k := by exact pow_succ' A k
      simp[this,Matrix.mul_assoc,ih]
      have : s^(k+1) = s^k*s := by rfl
      rw[this,mul_smul,h.right]

/- Next, we need to address a bit of a problem. When using a matrix in the definition of apply, above, we have the expression (p k) * (x^k.val) where x is a matrix. But we haven't defined multiplication * for a scalar times a matrix, only scalar multiplication • of a scalar times a matrix. And we can't change the definition to use •, because we might want to use the polynomial with other types. We can fix this by declaring an instances of HMul for scalars and matrices. Since we will just want to simplify this out in proofs, we add it to the simplifier so we can (hopefully) forget about it. -/

@[simp]
instance hmul_smul_inst {n m:ℕ} :
  HMul ℂ (Matrix (Fin n) (Fin m) ℂ) (Matrix (Fin n) (Fin m) ℂ)
  := ⟨ λ s A => s • A ⟩

/- # Theorem 1.16 : Eigenvalues of a Polynomial

Now we can state the theorem about eigenvalues of polynomials of matrices. Note that p.apply A would not typecheck without the above instance. -/

theorem eigen_pair_of_poly {n m:ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
                            {s : ℂ}
                            {v :  Matrix (Fin n) (Fin 1) ℂ}
                            (p : Poly ℂ m)
  : is_eigen_pair A s v → is_eigen_pair (p.apply A) (p.apply s) v  := by

    intro h
    unfold is_eigen_pair
    unfold is_eigen_pair at h
    unfold Poly.apply

    constructor

    . exact h.left

    . let f : Fin m → Matrix (Fin n) (Fin n) ℂ := fun k => p k * A ^ k.val
      have h0 : (∑ k : Fin m, p k * A ^ k.val ) * v
              = (∑ k : Fin m, f k ) * v := by simp[f]
      have h1 : (∑ k : Fin m, f k ) * v
              = ∑ k : Fin m, ( f k ) * v := by rw [Matrix.sum_mul]
      have h2 : (∑ k : Fin m, p k * s ^ k.val) • v
              = ∑ k : Fin m, (p k * (s ^ k.val)) • v := by rw [Finset.sum_smul]
      rw[h0,h1,h2]
      apply Finset.sum_congr rfl -- sums are equal if terms are equal
      intro k hk
      have : p k * A ^ k.val * v
           = p k * (A ^ k.val * v ) := by simp[hmul_smul_inst]
      rw[this,eig_eqn_pow k h]
      simp[hmul_smul_inst,smul_smul]

#print eigen_pair_of_poly

/- We can also define the eigenvalue property without the eigenvector, for convenience. -/

theorem eigen_val_of_poly {n m:ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
                            {s : ℂ}
                            (p : Poly ℂ m)
  : is_eigenvalue A s → is_eigenvalue (p.apply A) (p.apply s) := by

    intro ⟨ v, hv ⟩
    have hev : is_eigen_pair A s v := hv
    apply @eigen_pair_of_poly at hev
    exact eigen_value_from_pair (p.apply A) (p.apply s) v hev

/- # Example (p36) : Example polynomial of a matrix

Using our new tactic, we can prove a simple concrete example. -/

example {A : Matrix (Fin 2) (Fin 2) ℂ}
  : is_eigenvalue A (-1) → is_eigenvalue A 2
  → (is_eigenvalue (A^2) 1 ∧ is_eigenvalue (A^2) 4) := by

    intro h1 h2
    let p : Poly ℂ 3 := ![0,0,1]
    have g1 : p.apply A = A^2 := by small_poly p

    apply And.intro

    . have g0 := eigen_val_of_poly p h1
      have g2 : p.apply (-1) = 1 := by small_poly p
      simp_all[g1,g2]

    . have g0 := eigen_val_of_poly p h2
      have g2 : p.apply 2 = 4 := by
        small_poly p
        ring
      simp_all[g1,g2]

/- # Exercise (p36) : The eigenvalues of a diagonal matrix -/

def row
  {n m:ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (k:(Fin n))
  : Matrix (Fin 1) (Fin m) ℂ
  := Matrix.of (λ _ j => A k j)

def col
  {n m:ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (k:(Fin m))
  : Matrix (Fin n) (Fin 1) ℂ
  := Matrix.of (λ i _ => A i k)

def std_basis (n: ℕ) (k: (Fin n))
  : Matrix (Fin n) (Fin 1) ℂ
  := Matrix.of (λ i _ => if i=k then 1 else 0)

example {n:ℕ} (k:(Fin n))
  : row (1:Matrix (Fin n) (Fin n) ℂ) k = (col 1 k).transpose := by
  simp[row,col,Matrix.transpose,Matrix.one_apply,eq_comm]

theorem std_basis_col_id {n:ℕ} {k:(Fin n)}
  : col (1:Matrix (Fin n) (Fin n) ℂ) k = std_basis n k := by
  simp[std_basis,col,Matrix.one_apply]

theorem mul_std_basis
   {n:ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {k:(Fin n)}
   : A * std_basis n k = col A k := by
   simp[←std_basis_col_id,col]
   funext i j
   simp[Matrix.mul_apply,Matrix.one_apply]

theorem diag_eig_sys
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  : Matrix.IsDiag A → ∀ i , is_eigen_pair A (A i i) (std_basis n i) := by
  intro hdiag i
  constructor
  . rw[matrix_neq_exists]   -- show standard basis vector is not zero
    use i, i
    simp[std_basis]
  . simp[mul_std_basis]     -- show standard basis vector is an eigenvector
    simp[col,std_basis]
    aesop -- uses IsDiag

/- # Observation 1.17 : Having a zero eigenvalue is equivalent to being singular -/

def singular
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  := ∃ x : Matrix (Fin n) (Fin 1) ℂ, x ≠ 0 ∧ A*x = 0

def nonsingular
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  := ∀ x : Matrix (Fin n) (Fin 1) ℂ, A*x = 0 → x = 0

theorem sing_non_sing
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  : (¬singular A) ↔ (nonsingular A) := by
  simp[singular,nonsingular]
  constructor
  . intro h x hx
    exact not_imp_not.mp (h x) hx
  . intro h x hx hna
    exact hx (h x hna)

theorem eig_zero_to_non_sing
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  : is_eigenvalue A 0 ↔ singular A := by

    constructor
    . intro ⟨ v, ⟨ he, hz ⟩ ⟩
      simp at hz
      use v
    . intro ⟨ v, ⟨ hz, hv ⟩ ⟩
      exact ⟨ v, ⟨ hz, by simp; exact hv ⟩  ⟩

/- # Exercise 1 : Eigenvalues of the inverse -/

lemma mul_both_sides {n:ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} {u v: Matrix (Fin n) (Fin 1) ℂ}
 : A * u = v → B * A * u = B * v := by
   intro h
   rw[←h,Matrix.mul_assoc]

theorem eigen_inv
  {n:ℕ} {A:Matrix (Fin n) (Fin n) ℂ} [hia : Invertible A] {s:ℂ}
  : is_eigenvalue A s → is_eigenvalue A⁻¹ s⁻¹ := by
  intro ⟨ v, ⟨ vnz, hv ⟩ ⟩
  have snz : s ≠ 0 := by
    intro h
    rw[h,zero_smul] at hv
    have h1 : A⁻¹ * A * v = A⁻¹ * (0: Matrix (Fin n) (Fin 1) ℂ) := by
      apply mul_both_sides hv
    have h2 : A⁻¹ * (0: Matrix (Fin n) (Fin 1) ℂ) = 0 := by exact Matrix.mul_zero A⁻¹
    rw[h2] at h1
    simp at h1
    exact vnz h1
  use v
  constructor
  . exact vnz
  . have : A⁻¹ * A * v = A⁻¹ * (s • v) := by
      apply mul_both_sides hv
    have : v = s • (A⁻¹ * v) := by
      simp at this
      exact this
    have : s⁻¹ • v = (A⁻¹ * v) := by exact (inv_smul_eq_iff₀ snz).mpr this
    exact id (Eq.symm this)

/- # Exercise 2 : If the sum of each row is 1, then 1 is an eigenvalue -/

theorem sum_rows_one {n:ℕ} {hnp : n>0} {A : Matrix (Fin n) (Fin n) ℂ}
  : (∀ i : Fin n, ∑ j : Fin n, A i j = 1) → is_eigenvalue A 1 := by
    intro hi
    use Matrix.of (λ _ _ => 1)
    constructor
    . intro h
      simp[matrix_eq_all] at h
      exact h (by exact ⟨0, hnp⟩)
    . simp[matrix_eq_all]
      intro j k
      simp[Matrix.mul_apply]
      exact hi j

/- # Exercise 3 : Todo -/

/- # Exercise 4 : Todo -/

/- # Exercise 5 : Idempotent Matrices and their eigenvalues -/

lemma smul_congr {n: ℕ} {a b : ℂ} {v : Matrix (Fin n) (Fin 1) ℂ} (hnz : v ≠ 0)
  : a • v = b • v → a = b := by
  intro h
  rw[matrix_neq_exists] at hnz
  have ⟨i, ⟨ j, hij ⟩ ⟩ := hnz
  have : j = 0 := by exact Fin.fin_one_eq_zero j
  rw[this] at hij
  have h_eq : (a • v) i 0 = (b • v) i 0 := by rw [h]
  simp [Matrix.smul_apply, hij] at h_eq
  apply Or.elim h_eq
  . exact id
  . intro hv
    simp_all

theorem idempotent_zero_one {n:ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (s : ℂ)
  : A*A = A → is_eigenvalue A s → (s = 0 ∨ s = 1) := by

  intro h ha
  apply eq_zero_or_one_of_sq_eq_self
  rw[pow_two]

  let p : Poly ℂ 3 := ![0,0,1]
  obtain ⟨ v, ⟨ hnzv, hv ⟩ ⟩ := ha
  have hep : is_eigen_pair A s v := And.intro hnzv hv
  apply eigen_pair_of_poly p at hep
  have h1 : p.apply A = A*A  := by small_poly p; exact pow_two A
  have h2 : p.apply s = s*s  := by small_poly p; exact pow_two s
  simp[h1,h2] at hep
  obtain ⟨ h3, h4 ⟩ := hep
  simp[h,hv] at h4

  apply smul_congr hnzv at h4
  exact id (Eq.symm h4)

/- # Exercise 6 : Nilpotent Matrices and their eigenvalues -/

def monomial {R: Type*} [Ring R] (q:ℕ) : Poly R (q+1) :=
  λ i => if i < q then 0 else 1

lemma eigenval_of_power {n:ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {s : ℂ} {v: Matrix (Fin n) (Fin 1) ℂ} (q:ℕ)
  : is_eigen_pair A s v → is_eigen_pair (A^q) (s^q) v := by
  intro h
  constructor
  . exact h.left
  . let p : Poly ℂ (q+1) := monomial q

    have h3 : p.apply A = A^q := by -- TODO: this have and the next
      unfold p Poly.apply monomial  -- should be done via a lemma
      simp[Fin.sum_univ_castSucc]
      have : ∀ x : Fin q, x.castSucc < Fin.last q := by
        exact fun x ↦ Fin.castSucc_lt_last x
      simp[this]

    have h4 : p.apply s = s^q := by
      unfold p Poly.apply monomial
      simp[Fin.sum_univ_castSucc]
      have : ∀ x : Fin q, x.castSucc < Fin.last q := by
        exact fun x ↦ Fin.castSucc_lt_last x
      simp[this]

    apply eigen_pair_of_poly p at h
    simp[p,h3,h4] at h

    exact h.right

theorem nilpotent_zero_one {n:ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (s : ℂ)
  : (∃ q : ℕ , A^q = 0) → is_eigenvalue A s → s = 0 := by
    intro ⟨ q, hq ⟩ hs
    obtain ⟨ v, ⟨ hnzv, hv ⟩ ⟩ := hs
    have hep : is_eigen_pair A s v := And.intro hnzv hv
    apply eigenval_of_power q at hep
    obtain ⟨ h3, h4 ⟩ := hep
    have : (0 : Matrix (Fin n) (Fin n) ℂ) * v = (0:ℂ) • v := by simp
    rw[hq,this] at h4
    apply smul_congr hnzv at h4
    exact pow_eq_zero (id (Eq.symm h4))

/- # Exercise 7 : Todo -/

/- # Exercise 8 : Infinite dimensional example with no eigenvalues -/
-- Maybe this one is out of scope for this project?

/- # Exercise 9 :Todo -/
