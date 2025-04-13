import Mathlib

def orbit {α : Type*} (f : α → α) (x0 : α) (i : ℕ) := match i with
  | Nat.zero => x0
  | Nat.succ k => f (orbit f x0 k)

#check orbit id 0 123

def shift {α : Type*} (σ : ℕ → α) := λ k => σ (k+1)

theorem orbit_tail {α : Type*}  {f : α → α}  {x y : α} {n : ℕ}
  : orbit f x n = y → orbit f x (n+1) = f y := by
  intro h
  unfold orbit
  rw[h]

theorem orbit_tail_next {α : Type*}  {f : α → α}  {x y z : α} {n : ℕ}
  : orbit f x n = y → f y = z → orbit f x (n+1) = z := by
  intro h1 h2
  rw[←h2]
  apply orbit_tail
  exact h1

theorem orbit_comp  {α : Type*} {f : α → α}  {x : α} {n : ℕ}
  : orbit f (orbit f x 1) n = orbit f x (n+1) := by
  simp[orbit]
  induction n with
  | zero => simp[orbit]
  | succ k ih =>
    unfold orbit
    simp[ih]

theorem orbit_next_head {α : Type*}  {f : α → α}  {x y z : α} {n : ℕ}
  : f x = y → orbit f y n = z → orbit f x (n+1) = z := by
  intro h1 h2
  have : orbit f x 1 = y := h1
  rw[←this] at h2
  rw[orbit_comp] at h2
  exact h2
