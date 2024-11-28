/-
We define a function recursively for all positive integers $n$ by $f(1)=1$, $f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$. Show that $f(n)=$ $2^{n}+(-1)^{n}$, using the second principle of mathematical induction.
-/

import Mathlib

def f : Nat -> Nat
  | 0 => 0 -- unused case
  | 1 => 1
  | 2 => 5
  | x+3 => f (x+2) + 2 * f (x+1)

example (n : Nat) (h : n ≠ 0) : (f n : ℤ) = 2 ^ n + (-1) ^ n := by
  match n with
  | 0 => exact False.elim (h rfl)
  | n0+1 =>
    /- Two step induction -/
    have H : (f (n0 + 1) : ℤ) = 2 ^ (n0 + 1) + (-1) ^ (n0 + 1) ∧ (f (n0 + 2) : ℤ) = 2 ^ (n0 + 2) + (-1) ^ (n0 + 2) := by
      induction n0 with
      | zero =>
        simp [f]
      | succ n1 ih =>
        have ih' := ih (Nat.succ_ne_zero n1)
        apply And.intro
        . rw [add_assoc]
          rw [one_add_one_eq_two]
          exact ih'.right
        . simp [f]
          rw [ih'.left, ih'.right]
          ring
    exact H.left
