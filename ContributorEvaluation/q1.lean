import Mathlib

open Finset BigOperators

/-

If $a$ and $r$ are real numbers and $r \neq 1$, then
(1.1)
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1} .
$$
-/

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ Finset.range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  conv at h => rw [<-sub_ne_zero]
  induction n with
  | zero =>
    simp
    rw [<-mul_left_inj' h]
    rw [div_mul]
    rw [div_self h]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    rw [pow_add r (n+1)]
    rw [<-mul_left_inj' h]
    simp only [add_mul, div_mul, div_self h]
    ring
